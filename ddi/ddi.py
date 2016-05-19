from collections import namedtuple
import inspect
from inspect import getfullargspec, signature
from functools import wraps, partial
from itertools import islice
import fnmatch
import random

def NoAssertion(obj): return True

def update_args(func, args, kwargs, update):
    ret = (
        inspect.getfullargspec(func))

    arg_names = ret[0]
    args = list(args)
    
    for i, (name, val) in enumerate(zip(arg_names, args)):
        if name in update:
            args[i] = update[name]
            del update[name]
    
    kwargs.update(update)
        
    return args, kwargs

class Demander:
    
    def __init__(self, provider, inst_feature, args = (), kwargs = {}, deps={}, mask=[], feature=None):
        self.provider = provider
        self.feature = feature
        self.mask = mask
        self.inst_feature = inst_feature
        self.args = args
        self.kwargs = kwargs
        self.deps = deps
        self.dependencies = {}
        self.amendments = set()
        self.recurrent_dep = []
        self.simple_dep = []
        self.satisfied = {} # WeakValueDictionary() # set() #WeakValueDictionary()
        self.extract_dependencies()
        self.demanded_feature = []
                               
    def all_satisfied(self):
        return len(self.satisfied) == len(self.dependencies)
    
    def extract_dependencies(self):
        if self.dependencies:
            return True
        else:
            self.dependencies = {}            
            for arg_name, d in self.deps.items():
                self.dependencies[arg_name] = d
                if d.amendment:
                    self.amendments.add(arg_name)
            
            _, _, _, _, _, _, annotations = getfullargspec(self.provider)
                
            for arg_name, a in annotations.items():
                if isinstance(a, Dependency):
                    if arg_name not in self.dependencies:
                        self.dependencies[arg_name] = a

            for arg_name, a in self.dependencies.items():
                if anonymous(a.feature):
                    self.recurrent_dep.append((a, arg_name))
                else:
                    self.simple_dep.append(arg_name)
                    
                if a.amendment:
                    self.amendments.add(arg_name)

            return True

sep = '/'

def anonymous(feature):
    return (not feature) or (feature[-1] == sep)

class DemandedFeature:
    
    def __init__(self, demander, arg_name, dependecy, already_provided):
        self.demander = demander
        self.arg_name = arg_name
        self.dependency = dependecy
        if already_provided:
            self.provided(already_provided, ddic[already_provided])
        else:
            self.feature = None
    
    def provided(self, feature, provider):
        if (self.dependency.assertion(provider)):
            self.feature = feature
            self.demander.satisfied[self.arg_name] = (feature, provider) # .add(self.arg_name)
            return True
        else:
            return False

class DependencyContainer:
    
    def __init__(self, allowReplace=False, providers_cls = dict):
        super().__init__()
        self.providers_cls = providers_cls
        self.allowReplace = allowReplace
        self.clear()

    def __iter__(self):
        return self.providers.__iter__()
    
    def _provide(self, feature, provider):
        self.providers[feature] = provider
        self._provided_metadata[feature] = {'deps':[]}

    def filter(self, pat):
        for f in fnmatch.filter(self.providers.keys(), pat):
            yield f, self.providers[f]

    def clear(self):
        self.providers = self.providers_cls()
        self.configuration = []
        self._provided_metadata = {}
        self.demander_cnt = 0
        self._provide_candidates = []
        self._provided = []
        self._inst_level = 0
        self.demanders = []
        self.demanded_features = {}
        self.provided_last = {}

    def __setitem__(self, feature, provider):
        self.provide(feature, provider)

    def __delitem__(self, feature):
        self.unprovide(feature)

    def __getitem__(self, feature):
        return self.providers[feature]

    def __contains__(self, feature):
        try:
            _ = self[feature]
            return True
        except KeyError:
            return False

    def inst_demander(self, demander):
        args, kwargs = update_args(demander.provider, demander.args, demander.kwargs, {k:v for k, (_, v) in demander.satisfied.items()})

        if demander.inst_feature:
            args, kwargs = all2kwargs(demander.provider, args, kwargs)
            demander_inst_feature = demander.inst_feature
            
            if anonymous(demander_inst_feature):
                demander_inst_feature += str(random.randint(0, 1e8))
    
    #         kwargs = self.update_params_with_conf(demander.inst_feature, kwargs)
    #         args, params = all2kwargs(cls.__init__, args, kwargs, ignore_args_cnt=1)
            
            kwargs = ddic.update_params_with_conf(demander_inst_feature, kwargs)

        demander_inst = demander.provider(*args, **kwargs)
        if demander.inst_feature:
            try:
                for _, (feature, _) in demander.satisfied.items():
                    self._provided_metadata[feature]['deps'].append(demander_inst_feature)
            except KeyError:
                return None

            self.provide(demander_inst_feature, demander_inst)

            return demander_inst_feature
        else:
            return None

    def update_params_with_conf(self, feature, params):
        for p in params:
            pqname = '.'.join([feature, p])
            for pat, val in self.configuration:
                if fnmatch.fnmatch(pqname, pat):
                    params[p] = val
                    
        return params

    def configure(self, pat, val):
        self.configuration.append((pat, val))

    def provide(self, feature, provider):
        
        if not self.allowReplace:
            assert not (feature in self.providers), "Duplicate feature: %r" % feature

        feature_ext = feature

        if anonymous(feature):
            feature_ext += str(id(provider))
            
        if feature_ext[0] == sep:
            feature_ext = feature_ext[1:]

        self._provide(feature_ext, provider)
        
        self._inst_level += 1
        self._provide_candidates.append(set())
        self._provided.append(feature_ext)
        
        for pattern, df_list in self.demanded_features.items():
            if fnmatch.fnmatch(feature_ext, pattern):
                self.provided_last[pattern] = feature_ext
                for df in df_list:
                    self._provide_candidates[-1].add(df)
                    df.proposed = (feature_ext, provider)

        pc = True
        while pc is not None:
            for pc in sorted(self._provide_candidates[-1], key=lambda x: x.demander.id, reverse=True ):
                if pc.dependency.amendment:
                    if pc.provided(pc.proposed[0], pc.proposed[1]):
                        if pc.demander.all_satisfied():
                            break
            else:
                break

            self._provide_candidates[-1].remove(pc)
            self.inst_demander(pc.demander)
            
            

        pc = True
        while pc is not None:
            for pc in sorted(self._provide_candidates[-1], key=lambda x: x.demander.id, reverse=True ):            
                if not pc.dependency.amendment:
                    if pc.provided(pc.proposed[0], pc.proposed[1]):
                        if pc.demander.all_satisfied():
                            break
            else:
                break
            
            self._provide_candidates[-1].remove(pc)
            self.inst_demander(pc.demander)

        self._inst_level -= 1
        self._provide_candidates.pop()
        self._provided.pop()
         
        if self._inst_level == 0:
            self._provide_candidates.clear()
            self._provided.clear()
        
        return feature_ext
    
    def provide_on_demand(self, feature=None, provider=None, inst_feature=None, inst_args=(), inst_kwargs={}, deps={}, mask=[]):
#         assert inst_feature is not None, "Have to provide feature to be instantiated!"

        provider_supplied = True if provider is not None else False
        feature_supplied = True if feature is not None else False
        
        if not provider_supplied:
            provider = self[feature]
            
        demander = Demander(provider, inst_feature, list(inst_args), dict(inst_kwargs), deps, mask=list(mask), feature=feature)
        for name, d in demander.dependencies.items():
            already_provided = None
            
            if d.feature not in self.demanded_features:
                self.demanded_features[d.feature] = []
                
                for f_name in self:
                    if fnmatch.fnmatch(f_name, d.feature):
                        self.provided_last[d.feature] = f_name
                        already_provided = f_name
                        break
                #else:
#                    self.provided_last[d.feature] = None
                    
            else:
                if d.feature in self.provided_last:
                    already_provided = self.provided_last[d.feature]
            
            df = DemandedFeature(demander, name, d, already_provided)
            demander.id = self.demander_cnt
            self.demander_cnt += 1
            self.demanded_features[d.feature].append(df)
            demander.demanded_feature.append(df)
            
        self.demanders.append(demander)
        
        ret = [None, None]
        if provider_supplied and feature_supplied:
            ret[0] = self.provide(feature, provider)

        if demander.all_satisfied():
            ret[1] = self.inst_demander(demander)
            
        return tuple(ret)
        
    def unprovide_by_name(self, feature):
        if feature in self._provided_metadata:
            for f in self._provided_metadata[feature]['deps']:
                self.unprovide_by_name(f)
            
            del self._provided_metadata[feature]

        if feature in self.providers:
            del self.providers[feature]
    
    def unprovide(self, provider):
        for f, p in self.providers.items():
            if provider is p:
                feature = f
                break
        else:
            raise KeyError
        
        self.unprovide_by_name(feature)
        
#     def search(self, pat, assertion=NoAssertion):
#         for f,p in self.providers.items():
#             if fnmatch.fnmatch(f, pat):
#                 if assertion(p):
#                     yield f 
                    
    def search(self, pat='*', assertion=NoAssertion, depth=0):
        for f in fnmatch.filter(self.providers, pat):
            if assertion(self.providers[f]):
                yield f

ddic = DependencyContainer(allowReplace=True)

Dependency = namedtuple('Dependency', ['feature', 'assertion', 'amendment'])
Dependency.__new__.__defaults__ = (None, NoAssertion, False)

def Amendment(feature, assertion=NoAssertion):
    return Dependency(feature, assertion, True)

def lwraps(orig_func):
    
    def wrap(func):
        _, _, _, _, _, _, annotations = getfullargspec(orig_func)
        
        dependencies = {}
        
        for name, a in annotations.items():
            if isinstance(a, Dependency):
                dependencies[name] = a
                
        w = wraps(orig_func)(func)
        
        if dependencies:
            sig = signature(w)
            params = []
            for p in sig.parameters.values():
#                if p.name not in dependencies:
                params.append(p)
                     
            sig = sig.replace(parameters=tuple(params))
            w.__signature__ = sig
            
        return w
    
    return wrap
    

def diinit(func):
    _, _, _, _, _, _, annotations = getfullargspec(func)
    
    dependencies = {}
    
    for name, a in annotations.items():
        if isinstance(a, Dependency):
            dependencies[name] = a
    
    @lwraps(func)
    def wrapper(*args, **kwargs):
        dependency_kwargs = {}
        
        for name, a in dependencies.items():
            provider = ddic[a.feature]
            if a.assertion(provider):
                dependency_kwargs[name] = provider
                
        args, kwargs = update_args(func, args, kwargs, dependency_kwargs)
        
        return func(*args, **kwargs)

    if dependencies:
        sig = signature(wrapper)
        params = []
        for p in sig.parameters.values():
            if p.name not in dependencies:
                params.append(p)
                
            sig = sig.replace(parameters=tuple(params))
            wrapper.__signature__ = sig                

    return wrapper

def all2kwargs(func, args, kwargs, ignore_args_cnt=0):
    arg_names, varargs, varkw, defaults, kwonlyargs, kwonlydefaults, annotations = (
        inspect.getfullargspec(func))
    
    if inspect.isclass(func):
        arg_names = arg_names[1:]

    params = kwargs
    
    arg_names = arg_names[ignore_args_cnt:]
    
    if defaults:
        # Add all the arguments that have a default value to the kwargs
        for name, val in zip(reversed(arg_names), reversed(defaults)):
            if name not in params:
                params[name] = val

    for name, val in zip(arg_names, args):
        params[name] = val
        
    args = args[len(arg_names):]

    return args, params

# def compinit(func):
#     @diinit
#     @lwraps(func)
#     def wrapper(self, name, parent, *args, **kwargs):
#         if parent is None:
#             qname = name
#         else:
#             qname = sep.join([parent.qname, name])
#                     
#         args, params = all2kwargs(func, args, kwargs, ignore_args_cnt=3)
#         
#         params = ddic.update_params_with_conf(qname, params)
#         
#         self.name = name
#         self.qname = qname
#         func(self, name, parent, *args, **params)
#         
#         ddic.provide(qname, self)        
        
#     def wrapper(self, name=None, parent=None, *args, **kwargs):
#         
#         if func.__name__ != '__init__':
#             raise Exception('Decorated function must be __init__().')
# 
#         params = all2kwargs(func, self, *args, name=name, parent=parent, **kwargs)
#         if self.__cur_parent_class__ is None:
#             if (parent is not None) and (name is not None):    
#             
#                 parent[name] = self
#                 qname = sep.join([parent.qname, name])
#                 
#                 sydsys()[qname] = self
#                 
#                 sys_conf = sydsys().get_all_attrs(qname)
#                 
#                 for n, v in sys_conf.items():
#                     params[n] = v
#                     
#     #             arg_names, varargs, varkw, defaults = (
#     #                                                    inspect.getargspec(func))
#     #             
#     #             if defaults:
#     #                 for arg_name, _ in zip(reversed(arg_names), reversed(defaults)):
#     #                     setattr(self, arg_name, params[arg_name])
#         
#             self.__cur_parent_class__ = self.__class__
#             
#         self.__cur_parent_class__ = self.__cur_parent_class__.__bases__[0] 
#         self.__cur_parent_class__.__init__(**params)
# 
#         func(**params)
        
    return wrapper
