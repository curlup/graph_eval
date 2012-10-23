#!/usr/bin/python

"""
Module provides tools for defenition of evaluation graphs
"""
__VERBOSE = False

from functools import wraps, partial
from collections import defaultdict, namedtuple
from itertools import groupby

Node = namedtuple("Node", "value requests requested")

def defgraph(graph):
	"""
	helps to create "dependency" graphs like
	@defgraph
	def my_graph(introduce_node):
		introduce_node(None, 'root', [])

		@partial(introduce_node, name = 'my_class', dependencies=['root'])
		class _class(object):
			is_2 = False

		@partial(introduce_node, name = 'my_class2', dependencies=['root','my_class'])
		class _class(object):
			is_2 = True

	you got {
	'root': Node(None),
	'my_class':Node(_class, requests=['root']),
	'my_class2':Node(_class, requests=['root', 'my_class']),
	}

	do whatever you want or see defnk for evaluation dependent functions graph example
	"""
	_graph = defaultdict(lambda : dict(value = None, requests = set(), requested = list()))

	def node(node, name, dependencies):
		"""
		internal func of defgraph. see defgraph.
		"""
		assert name not in _graph, "two nodes with same name"
		_graph[name]['value'] = node 

		for dep in dependencies:
			_graph[dep]['requested'].append(name)

			assert name not in _graph[dep]['requests'], "no cyclic dependencies allowed: {0} -> {1} -> {0}".format(dep, name)
		_graph[name]['requests'].update(dependencies)

	res = graph(node)
	assert res is None, "No return value must be provided for 'defgraph' func."

	return dict( (k, Node(**v)) for k,v in _graph.items())

def defnk(func_graph):
	"""
	use it like
	@defnk
	def graph(defn):
		@defn
		def n(xs):
			return float(len(xs))

		@defn
		def m(xs,n):
			return sum(xs)/n

		@defn
		def m2(xs,n):
			return sum(x**2 for x in xs)/n

		@defn
		def var(m, m2):
			return m2 - m**2

	not tested with default params and *args, **kwargs

	returns -> {
	'xs': Node(),
	'n':  Node(request=[xs]),
	'm':  Node(request=[xs,n]),
	'm2': Node(request=[xs,n]),
	'var':Node(request=[m,m2])
	}
	"""
	def graph(node):
		def defn(func):
			nodename = func.func_name
			dependencies = func.func_code.co_varnames
			return node(func, nodename, dependencies)
		return func_graph(defn)

	return defgraph(graph)
	
def topsort(graph):
	"""
	topological sorting of graph from defgraph by requests
	returns -> [
		['layer1_var','layer1_var2'], #free vars
		['layer2_var'], #dependent on layer1
		['layer3_var'], #dependent on layer2
	]
	"""

	toposorted_vars = []
	_toposorted = {}

	def deep_walk(name):
		if name in _toposorted:
			return _toposorted[name]

		node = graph[name]
		
		if len(node.requests) == 0:
			level = 0 #free var'
		else:
			level = 1+max(deep_walk(child) for child in node.requests)

		_toposorted[name] = level
		toposorted_vars.append((level, name))
		return level

	for name in graph:
		deep_walk(name) 

	topsorted_layers = []
	for k,sub_i in groupby(sorted(toposorted_vars), lambda x:x[0]):
		topsorted_layers.append([var for k,var in sub_i])

	return topsorted_layers

def graph_free_vars(graph):
	"""
	returns "free" vars that should provided for computation
	"""
	return set(k for k,v in graph.items() if v.value is None)

def _assert_free_vars(free_vars, kw):
	assert all(k in free_vars for k in kw), ('you' + 
		' should provide only {0} as key-vakue args for computation'
		).format(', '.join(free_vars))
	return kw

def defnk_compile2func(graph):
	"""
	see main() here for usage example
	returns function that compute all defnk graph from **kw dict
	"""
	free_vars = graph_free_vars(graph)
	def f(**kw):
		"""
		TODO with .format for f **kw params
		"""
		got = _assert_free_vars(free_vars, kw)
		not_provided = free_vars.difference(kw)
		assert len(not_provided) == 0, ('takes exactly {0} keyword args, "{1}" not given'.
			format(len(free_vars), '", "'.join(not_provided)))

		res = {}
		gen = graph_compile2gen(graph, **kw)
		try:
			jobs = gen.next()
			while True:
				partial_res = dict( (j_key, j_func(**j_env)) for j_key, j_func, j_env in jobs)
				res.update(partial_res)
				jobs = gen.send(partial_res) 
		except StopIteration:
			pass
		return res

	return f

def defnk_compile2lazyfunc(graph):
	"""
	returns function that compute only needed nodes of defnk graph from **kw dict
	"""
	free_vars = graph_free_vars(graph)
	def f(*args, **kw):
		"""
		TODO with .format for f *arg **kw params
		"""
		got = _assert_free_vars(free_vars, kw)
		order = list(args)
		while not all(asked in got for asked in args):
			item = order.pop()
			if item in got:
				continue

			not_provided_for_item = [req for req in graph[item].requests if req not in got]
			if len(not_provided_for_item) > 0:
				assert not any(req in free_vars for req in not_provided_for_item)
				order.append(item)
				order.extend(not_provided_for_item)
			else:
				env = dict((req,got[req]) for req in graph[item].requests)
				func = graph[item].value
				if __VERBOSE: print 'about to eval', func
				res = func(**env)
				got[item]=res

		assert len(order) == 0
		return dict((asked, got[asked]) for asked in args)
		
	return f


def graph_compile2gen(graph, **kw):
	"""
	see main() here for usage example
	returns generator which requests some partial (one node) computation (which can be evaluated in any way. distributed over cluster for example) in order to compute full graph
	"""
	free_vars = graph_free_vars(graph)
	got = _assert_free_vars(free_vars, kw)
	waiting = set()
	graph_keys = set(graph)
	while graph_keys.symmetric_difference(got):
		new_to_ask = [
			k for k,v in graph.items() 
			if k not in got 
			and k not in waiting
			and all(w in got for w in v.requests)
		]
		if __VERBOSE: print 'about to ask', new_to_ask
		
		waiting.update(new_to_ask)
		just_got = yield [
			(
				k,
				graph[k].value, 
				dict((w,got[w]) for w in graph[k].requests)
			) 
			for k in new_to_ask
		]

		if __VERBOSE: print 'got', list(just_got)

		for k in just_got:
			waiting.remove(k)
			got[k] = just_got[k]
		

@defnk
def graph(defn):
	@defn
	def n(xs):
		return float(len(xs))

	@defn
	def m(xs,n):
		return sum(xs)/n

	@defn
	def m2(xs,n):
		return sum(x**2 for x in xs)/n

	@defn
	def var(m, m2):
		return m2 - m**2

	
def main():
	print 'compiled graph'
	for k, el in graph.iteritems():
		print k, el

	print '\nserial run graph_compile2gen'
	try:
		compiled = graph_compile2gen(graph, xs=range(10))
		jobs = compiled.next()
		while True:
			j_key, j_func, j_env = jobs.pop()
			jobs.extend(compiled.send({j_key: j_func(**j_env)}))

	except StopIteration:
		print j_env

	print '\nparallel run graph_compile2gen'
	try:
		compiled = graph_compile2gen(graph, xs=range(10))
		jobs = compiled.next()
		while True:
			jobs = compiled.send(dict( (j_key, j_func(**j_env)) for j_key, j_func, j_env in jobs)) 

	except StopIteration:
		print j_env

	print '\ncompiled with defnk_compile2func'
	graph_func = defnk_compile2func(graph)
	try:
		graph_func()
	except Exception, e:
		print '{0}: {1}'.format(e.__class__.__name__, e)
	print graph_func(xs=range(10))

	print '\ncompiled with defnk_compile2lazyfunc'
	graph_lazyfunc = defnk_compile2lazyfunc(graph)
	print graph_lazyfunc('m2','n', xs=range(10))


if __name__ == '__main__':
	global __VERBOSE

	__VERBOSE = True
	print 'some example code run\n'
	main()