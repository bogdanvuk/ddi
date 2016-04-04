from collections import namedtuple
import inspect
from inspect import getfullargspec, signature
from weakref import WeakValueDictionary
from PyQt5 import QtCore
from functools import wraps, partial
from itertools import islice
import fnmatch

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
        self.instances = {}
        self.dependencies_by_feature = {}
        self.satisfied = {} # WeakValueDictionary() # set() #WeakValueDictionary()
        self.extract_dependencies()
        self.demanded_feature = []
#             for name, d in self.dependencies.items():
#                 if d.feature in ddic:
#                     self.satisfied_on_feature_provided(d.feature, ddic[d.feature])
                        
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

    def all_simple_satisfied(self):
        return len(self.satisfied) == len(self.simple_dep)

    def simple_dep_satisfied(self, feature, dep_name):
        dep = self.dependencies[dep_name]
        if (feature == dep.feature) and \
            (dep_name not in self.satisfied) and \
            (feature in ddic):
            provider = ddic[feature]
            if (dep.assertion(provider)):
                return True
            
        return False

    def recurrent_dep_satisfied(self, feature, provider, dep, dep_name):
#         dep = self.dependencies[dep_name]
        if ((feature_scope(feature) + '/') == dep.feature):# and \
#            (feature in ddic):
#             provider = ddic[feature]
            if (dep.assertion(provider)):
                return True

        return False

    def feature_provided_for_simple_dep(self, feature, amend=False):
        if self.all_simple_satisfied():
            return None
        
        for dep_name in self.simple_dep:
            dep = self.dependencies[dep_name]
            if dep.amendment == amend:
                if self.simple_dep_satisfied(feature, dep_name):
                    self.satisfied.add(dep_name)
                    return dep_name
            
        return None
    
    def feature_unprovided_for_simple_dep(self, feature):
        for dep_name in self.simple_dep:
            dep = self.dependencies[dep_name]
            if dep.feature == feature:
                self.satisfied.remove(dep_name)
            
    def feature_provided_for_recurrent_dep(self, feature, provider, forbidden=[], amend=False):
        for dep, dep_name in self.recurrent_dep:
#             dep = self.dependencies[dep_name]
            if dep.amendment == amend:
                if (feature,dep_name) not in forbidden:
                    if self.recurrent_dep_satisfied(feature, provider, dep, dep_name):
                        return dep_name
            
        return None

    def check_unsatisfied_simple_dep(self):
        for dep_name in self.simple_dep:
            dep = self.dependencies[dep_name]
            if self.simple_dep_satisfied(dep.feature, dep_name):
                self.satisfied.add(dep_name)
                
#         newly_satisfied = False
#         for feature in self.simple_dep:
#             if (not feature in self.satisfied) and (feature in ddic):
#                 provider = ddic[feature]
#                 if self.dependencies_by_feature[feature].assertion(provider):
#                     self.satisfied.add(feature) #] = provider
#                     newly_satisfied = True
#                     
#         return newly_satisfied

    def satisfied_on_recurrent_features(self, features, forbidden = [], amend=False):
        recurrent_dep_satisfied = {}
        for f, p in features:
            dep_name = self.feature_provided_for_recurrent_dep(f, p, forbidden, amend)
            if dep_name is not None:
                recurrent_dep_satisfied[dep_name] = f

        return recurrent_dep_satisfied

#     def satisfied_on_feature_provided(self, feature, provider):
#         if self.extract_dependencies():
#             if feature in self.satisfied:
#                 del self.satisfied[feature]
# 
#             if feature in self.dependencies_by_feature:
#                 if self.dependencies_by_feature[feature].assertion(provider):
#                     self.satisfied[feature] = provider
#                     
#                 return self.all_satisfied()
#             elif (feature_scope(feature) + '/') in self.dependencies_by_feature:
#                 if self.dependencies_by_feature[feature_scope(feature) + '/'].assertion(provider):
#                     self.satisfied[feature_scope(feature) + '/'] = provider
#                     return self.all_satisfied()
# 
#         return False
                
# Demander = namedtuple('Demander', ['feature', 'inst_feature', 'args', 'kwargs'])
# Demander.__new__.__defaults__ = (None, None, (), {})

sep = '/'

class DependencyScope(QtCore.QObject):
    
    provided = QtCore.pyqtSignal(QtCore.QObject, str)
    
    def __init__(self, name, parent=None, providers_cls = dict):
        super().__init__()
        self.providers = providers_cls()
        self._provided_metadata = {}
        self.parent = parent
        self.name = name

    @property
    def uri(self):
        if self.parent:
            uri = self.parent.uri + [self.name]
        else:
            uri = [self.name]
            
        return uri

    def create_scope(self, feature):
        parent_scope_name, scope_base_name = split_feature(feature)
        scope = DependencyScope(name=feature)
        self[feature] = scope
        if parent_scope_name:
#             self[parent_scope_name][scope_base_name] = scope  
            scope.parent = self[parent_scope_name]
        else:
#             self[scope_base_name] = scope  
            scope.parent = self
           
        return scope
    
#     def provide_on_demand(self, feature, provider=None, inst_feature=None, inst_args=(), inst_kwargs={}):
#         self.parent.provide(self.name + '.' + self.feature, provider, inst_provider)
    
    def __iter__(self):
        return self.providers.__iter__()
    
    def _provide(self, feature, provider):
        self.providers[feature] = provider
        self._provided_metadata[feature] = {'deps':[]}
#         scope, base = split_feature(feature)
#         
#         if scope:
#             try:
#                 self[scope]._provide(base, provider)
#             except KeyError:
#                 self.create_scope(scope)
#                 self[scope]._provide(base, provider)
#         else:
#             if base.isnumeric():
#                 base = int(base)
# 
#             self.providers[base] = provider
#             self.provided.emit(self, str(base))

    def unprovide(self, feature):
        self.parent.unprovide(sep.join([self.name, feature]))

    def provide(self, feature, provider):
        self.parent.provide(sep.join([self.name, feature]), provider)
    
    def __setitem__(self, feature, provider):
#         self._provide_intern(feature, provider)
        self.provide(feature, provider)

    def __delitem__(self, feature):
        scope, base = split_feature(feature)
        
        if scope:
            del self[scope][base]
        else:
            if base.isnumeric():
                base = int(base)

            del self.providers[base]

    def __getitem__(self, feature):
        try:
            return self.providers[feature]
        except KeyError:
            raise KeyError("Unknown feature named {0}".format(feature))

        scope, base = split_feature(feature)
        try:
            if scope:
                return self[scope][base]
            else:
                if base.isnumeric():
                    base = int(base)

                return self.providers[base]

        except KeyError:
            raise KeyError("Unknown feature named {0}".format(feature))

    def __contains__(self, feature):
        try:
            _ = self[feature]
            return True
        except KeyError:
            return False
        

def anonymous(feature):
    return feature[-1] == sep

def split_feature(feature):
    if isinstance(feature, int):
        return '', feature
    else:
        segments = feature.rpartition(sep)
        
        if segments[-1]:
            return segments[0], segments[-1]
        else:
            if segments[1]:
                return segments[0], ''
            else:
                return '', segments[0]


def feature_base(feature):
    return split_feature(feature)[1]

def feature_scope(feature):
    return split_feature(feature)[0]


class DemandedFeature(object):
    
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

class DependencyContainer(DependencyScope):
    
    def __init__(self, allowReplace=False):
        DependencyScope.__init__(self, name=None, parent=None)
        self._provided_together = []
        self.demander_cnt = 0
        self._provide_candidates = []
        self._provided = []
        self._amended_together = []
        self._inst_level = 0
        self.demanders = []
        self._demanders_to_inst = []
        self.allowReplace = allowReplace
        self.provide_loop_mutex = False
        self.demanded_features = {}
        self.provided_last = {}

#     def create_scope(self, feature):
#         super().create_scope(feature)
#         self._provided_together.append(feature)
#         self._register_simple_dep(feature)
#        self.check_demands(feature, scope)

    def filter(self, pat):
        for f in fnmatch.filter(self.providers.keys(), pat):
            yield f, self.providers[f]

    def inst_demander(self, demander, recurrent_dep_satisfied={}, provide_intern=True):
#         dependencies = {}
#         for dep_name in demander.simple_dep:
#             dep = demander.dependencies[dep_name]
#             dependencies[dep_name] = self[dep.feature]
#             dependencies[d] = demander.satisfied[demander.dependencies[d].feature]
        
#         for d, f in recurrent_dep_satisfied.items():
#             dependencies[d] = self[f]

        args, kwargs = update_args(demander.provider, demander.args, demander.kwargs, {k:v for k, (_, v) in demander.satisfied.items()})
        demander_inst = demander.provider(*args, **kwargs)
        if demander.inst_feature:
            
#             demander_inst._dependents = {}
#             if provide_intern:
#                 demander_inst_feature = self._provide_intern(demander.inst_feature, demander_inst)
#             else:
            try:
                demander_inst_feature = demander.inst_feature
                if anonymous(demander_inst_feature):
                    demander_inst_feature += str(id(demander_inst))
                    
                for _, (feature, _) in demander.satisfied.items():
                    self._provided_metadata[feature]['deps'].append(demander_inst_feature)
            except KeyError:
                return None

            demander_inst_feature = self.provide(demander.inst_feature, demander_inst)

#             self._proviers_
            return demander_inst_feature
        else:
            return None
#             demander.instances[demander_inst_feature] = list(recurrent_dep_satisfied.values()) + [demander.dependencies[d].feature for d in demander.simple_dep]
#         return demander_inst, demander_inst_feature 

#             for _, dep_provider in dependencies.items():
#                 if not hasattr(dep_provider, '_dependents'):
#                     dep_provider._dependents = {}
#                     
#                 dep_provider._dependents[demander_inst_feature] = demander_inst

    def check_and_inst_demander(self, d, feature, provider = None, already_inst = set()):
        if not d.all_satisfied():
            if d.check_unsatisfied_simple_dep():
                if d.all_satisfied():
                    self.inst_demander(d)
                    return

            if d.all_simple_satisfied() and (not d.all_satisfied()):
                if d.satisfied_on_recurrent_feature_provided(feature):
                    self.inst_demander(d, feature)

    def _unregister_dep(self, feature):
        for_removal = []
        for d in reversed(self.demanders):
            d.feature_unprovided_for_simple_dep(feature)

            for name, deps in d.instances.items():
                if feature in deps:
                    for_removal.append((d, name))

        for d, name in for_removal:
            del d.instances[name]
        for d, name in for_removal:
            self.unprovide(name)

    def _register_simple_dep(self, feature, amend=False):
        _demanders_to_inst = []
        for d in reversed(self.demanders):
            if not d.all_satisfied():
                d.feature_provided_for_simple_dep(feature, amend)
                
                if d.all_satisfied():
                    _demanders_to_inst.append(d)
                    
        return _demanders_to_inst
#                     self.inst_demander(d)

    def check_demands(self, amend = False):
        
        for i, d in reversed(list(enumerate(self.demanders))):
            if d.inst_feature == 'ca_interpreter':
                pass
#             if i not in self._recurrent_demanders_fired:
            if d.all_simple_satisfied() and (not d.all_satisfied()):
                if i not in self.forbidden:
                    self.forbidden[i] = []

                recurrent_dep_satisfied = d.satisfied_on_recurrent_features(self._provided_together, self.forbidden[i], amend)
                if len(recurrent_dep_satisfied) == len(d.recurrent_dep):
#                     self._recurrent_demanders_fired.append(i)
                    
                    for k, v in recurrent_dep_satisfied.items(): 
                        self.forbidden[i].append((v, k))
                    
                    self.inst_demander(d, recurrent_dep_satisfied)

#             self.check_and_inst_demander(d)

    def _provide_loop(self, feature, provider):
        self._provided_together = []
        self._check_all_deps = []
        self._recurrent_demanders_fired = []
        provided_cnt = 0
        feature_ext = self._provide_intern(feature, provider)
        self._check_all_deps = list(self._provided_together) 
        
        while (provided_cnt < len(self._provided_together)):
            provided_cnt_old = provided_cnt
            provided_cnt = len(self._provided_together)
            
#             for feature in islice(self._provided_together, provided_cnt_old, provided_cnt):
#                 self._register_simple_dep(feature, amend=True)

            for feature in islice(self._provided_together, 0, provided_cnt):
                self._register_simple_dep(feature, amend=True)
                
            self.check_demands(amend=True)
            self._check_all_deps.extend(self._provided_together[provided_cnt:])
            while (self._check_all_deps and len(self._provided_together) == provided_cnt):
                self._register_simple_dep(self._check_all_deps.pop(), amend=False)
                self.check_demands(amend=False)
    
        return feature_ext
    
    def _provide_intern(self, feature, provider):
        #feature_ext = self._adjust_feature_and_provide(self, feature, provider)
        feature_ext = feature

        if anonymous(feature):
            feature_ext += str(id(provider))
            
        if feature_ext[0] == sep:
            feature_ext = feature_ext[1:]

        self._provide(feature_ext, provider)
        self._provided_together.append((feature_ext, provider))        
        
        return feature_ext
    
    def inst_demanders_on_simple_dep(self, feature_ext, amend):
        demander_instantiated = True
        while (demander_instantiated):
            demanders_to_inst = self._register_simple_dep(feature_ext, amend=amend)
            
            for d in demanders_to_inst:
                self.inst_demander(d)
            
            demander_instantiated = (len(demanders_to_inst) > 0)    
    
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
        
#         if self._inst_level == 0:
#             self._provided_together = []
#             self.forbidden = {}
        if feature_ext == 'win':
            pass

        for pattern, df_list in self.demanded_features.items():
            if fnmatch.fnmatch(feature_ext, pattern):
                for df in df_list:
#                     provide_candidates.append(df)
                    if (feature_ext, df.demander.feature) == ('view/actions.py', 'cls/ipython_editor_ast_manager'):
                        pass
                    
#                     self._provide_candidates[-1][(df.arg_name, df.demander.feature)] = df
                    self._provide_candidates[-1].add(df)
                    df.proposed = (feature_ext, provider)

#                     df.provided(feature_ext, provider)
#                     if df.demander.all_satisfied():
#                         provide_candidates[df.demander.feature] = df
        
#         ut.sort(key=lambda x: x.count, reverse=True)
        
#         filtered = []
#         for name, pc in self._provide_candidates[-1].items():
#             for pat in pc.demander.mask:
#                 for (provider_feature, demander_feature) in self._provide_candidates[-1]:
#                     if fnmatch.fnmatch(demander_feature, pat):
#                         filtered.append((provider_feature, demander_feature))
#                         
#         for f in filtered:
#             del self._provide_candidates[-1][f]

        
#         self._provide_candidates.update(provide_candidates)
       
#         for i, (_, pc) in enumerate(self._provide_candidates.items()):
        pc = True
        while pc is not None:
#             for name, pc in self._provide_candidates[-1].items():
            for pc in sorted(self._provide_candidates[-1], key=lambda x: x.demander.id, reverse=True ):
                if pc.dependency.amendment:
                    if pc.provided(pc.proposed[0], pc.proposed[1]):
                        if pc.demander.all_satisfied():
                            break
            else:
                break
            
#             del self._provide_candidates[-1][name]
            self._provide_candidates[-1].remove(pc)
            self.inst_demander(pc.demander)
            
#         for i, (_, pc) in enumerate(self._provide_candidates.items()):
        pc = True
        while pc is not None:
#             for name, pc in self._provide_candidates[-1].items():
            for pc in sorted(self._provide_candidates[-1], key=lambda x: x.demander.id, reverse=True ):            
                if not pc.dependency.amendment:
#                     if name == ('view/actions.py', 'cls/ipython_editor_ast_manager'):
#                         pass
                    if pc.demander.feature == 'cls/content_assist':
                        pass
                    if pc.provided(pc.proposed[0], pc.proposed[1]):
                        if pc.demander.all_satisfied():
                            break
            else:
                break
            
#             del self._provide_candidates[-1][name]
            self._provide_candidates[-1].remove(pc)
            self.inst_demander(pc.demander)

#         for _, pc in provide_candidates.items():
#             if not pc.dependency.amendment:
#                 df.provided(feature_ext, provider)
#                 if df.demander.all_satisfied():
#                     del provide_candidates[feature]
#                     self.inst_demander(pc.demander)
                
#                 pass
        
#         self._provided_together.append((feature_ext, provider))        
# 
        
#         self.inst_demanders_on_simple_dep(feature_ext, True)
#         self.check_demands(amend=True)
# 
#         self.inst_demanders_on_simple_dep(feature_ext, False)
#         self.check_demands(amend=False)
# 
        self._inst_level -= 1
        self._provide_candidates.pop()
        self._provided.pop()
         
        if self._inst_level == 0:
            self._provide_candidates.clear()
            self._provided.clear()
#             self._provided_together.clear()
#             self.forbidden.clear()
        
        return feature_ext

#         if not self.provide_loop_mutex:
#             self.provide_loop_mutex = True
#             ret = self._provide_loop(feature, provider)
#             self.provide_loop_mutex = False
#             return ret
#         else:
#             return self._provide_intern(feature, provider)

    
    def provide_on_demand(self, feature=None, provider=None, inst_feature=None, inst_args=(), inst_kwargs={}, deps={}, mask=[]):
#         assert inst_feature is not None, "Have to provide feature to be instantiated!"

        provider_supplied = True if provider is not None else False
        feature_supplied = True if feature is not None else False
        
        if not provider_supplied:
            provider = ddic[feature]
            
        demander = Demander(provider, inst_feature, list(inst_args), dict(inst_kwargs), deps, mask=list(mask), feature=feature)
        for name, d in demander.dependencies.items():
            if d.feature not in self.demanded_features:
                self.demanded_features[d.feature] = []
                
                for f_name in ddic:
                    if fnmatch.fnmatch(f_name, d.feature):
                        self.provided_last[d.feature] = f_name
                        already_provided = f_name
                        break
                else:
                    self.provided_last[d.feature] = None
                    already_provided = None
            else:
                already_provided = self.provided_last[d.feature]
            
            df = DemandedFeature(demander, name, d, already_provided)
            demander.id = self.demander_cnt
            self.demander_cnt += 1
            self.demanded_features[d.feature].append(df)
            demander.demanded_feature.append(df)
            
#         demander.check_unsatisfied_simple_dep()

        self.demanders.append(demander)
        
#         for a in demander.amendments:
#             dep = demander.dependencies[a]
#             self.amendments[dep.feature]
        
        if provider_supplied and feature_supplied:
            self.provide(feature, provider)

        if demander.all_satisfied():
            self.inst_demander(demander, provide_intern=False)
        
#         
#         if demander.all_satisfied():
#             self.inst_demander(demander)
#         elif len(demander.dir_dependencies) == 1:
#             dir_dep = demander.dir_dependencies[0]
#             dir_feature = feature_scope(dir_dep) 
#             if dir_feature in self:
#                 for f in self[dir_feature]:
#                     self.check_and_inst_demander(demander, dir_dep + f)
#         else:
#             self.check_and_inst_demander(demander, feature)
    
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
        
    def search(self, pat, assertion=NoAssertion):
        for f,p in self.providers.items():
            if fnmatch.fnmatch(f, pat):
                if assertion(p):
                    yield f 
        
#         self._unregister_dep(feature)
    
#     def create_on_demand(self, feature, inst_feature=None, args=(), kwargs={}):
#         self.demanders.append(Demander(feature, inst_feature, list(args), dict(kwargs)))

ddic = DependencyContainer(allowReplace=True)

class RequiredFeature(object):
    def __init__(self, feature, assertion=NoAssertion):
        self.feature = feature
        self.assertion = assertion
    def __get__(self, obj, T):
        return self.result # <-- will request the feature upon first call
    def __getattr__(self, name):
        assert name == 'result', "Unexpected attribute request other then 'result'"
        self.result = self.Request()
        return self.result
    def Request(self):
        obj = ddic[self.feature]
        assert self.assertion(obj), \
                 "The value %r of %r does not match the specified criteria" \
                 % (obj, self.feature)
        return obj

class CreationFeature(object):
    def __init__(self, feature=None, feature_scope='', assertion=NoAssertion):
        self.feature = feature
        self.assertion = assertion
        ddic.register_creation_dependency(self)
    def __get__(self, obj, T):
        return self.result # <-- will request the feature upon first call
    def __getattr__(self, name):
        assert name == 'result', "Unexpected attribute request other then 'result'"
        self.result = self.Request()
        return self.result
    def Request(self):
        obj = ddic[self.feature]
        assert self.assertion(obj), \
                 "The value %r of %r does not match the specified criteria" \
                 % (obj, self.feature)
        return obj

Dependency = namedtuple('Dependency', ['feature', 'assertion', 'amendment'])
Dependency.__new__.__defaults__ = (None, NoAssertion, False)

def Amendment(feature, assertion=NoAssertion):
    return Dependency(feature, assertion, True)

def diinit(func):
    _, _, _, _, _, _, annotations = getfullargspec(func)
    
    dependencies = {}
    dep_dflts = {}
    
    for name, a in annotations.items():
        if isinstance(a, Dependency):
            dependencies[name] = a
            dep_dflts[name] = None

#     if dep_dflts:
#         func = partial(func, **dep_dflts)

    @wraps(func)
    def wrapper(*args, **kwargs):
#         print('HERE!')
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

    return wrapper #wraps(wrapper)(func) 

#      
# class Test:
#     def __init__(self, a, b: Dependency(feature='scope.'), c: Dependency(feature='mark')):
#         self.b = b
#         self.c = c
#   
# class Test1:
#     def __init__(self, a, b: Dependency(feature='scope.'), c: Dependency(feature='scope.subscope.')):
#         self.b = b
#         self.c = c
#   
#       
# class Mark:
#     pass
#   
# def bla():
#     pass    
#   
# ddic.provide('test', Test, '.', inst_args=(1,))
#   
# ddic.provide('mark', Mark)
# ddic.create_scope('scope')
# ddic.provide('scope.test1', Test1, 'scope.subscope.Test1', inst_args=(1,))
#   
# ddic.create_scope('scope.subscope')
# ddic.provide('scope.', bla)
# ddic.provide('scope.subscope.', bla)
#  
# ddic.unprovide('scope.' + str(id(bla)))
#   
# pass
