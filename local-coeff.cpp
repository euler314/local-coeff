// Computes the local clustering coefficient of a graph.
// 
// (1) The graph is given in DIMACS format.
// (2) Uses the brute-force algorithm, but is fast enough for small graphs.

#include <iostream>
#include <vector>
#include <algorithm>
#include <numeric>
#include <iterator>
#include <sstream>
#include <string>
#include <fstream>
#include <cassert>
#include <cstdint>

typedef std::uint64_t index_t;

#include <chrono>
#include <unordered_set>
#include <boost/functional/hash.hpp>

typedef std::unordered_set<std::pair<index_t, index_t>, 
	boost::hash< std::pair<index_t, index_t> >  > edge_set;

static index_t *enlarge(index_t m, index_t m_was, index_t *was)
{
	assert(m >= 0 && m_was >= 0);

	index_t* a = new index_t[m];

	if (was)
	{
		for (index_t i = 0; i < m_was; ++i)
		{
			a[i] = was[i];
		}

		delete was;
	}

	return a;
}

struct graph
{
	graph(index_t n) : num_vertices(n), num_edges(0), edge_capacity(1024)
	{
		edges = enlarge(2 * edge_capacity, 0, 0);
	}

	graph& operator=(const graph&) = delete;

	~graph()
	{
		delete edges;
	}

	index_t num_vertices;
	index_t num_edges;
	index_t edge_capacity;
	index_t *edges;
};

void graph_add_edge(graph& g, index_t u, index_t v)
{
	assert(u >= 0 &&
		v >= 0 &&
		u != v &&
		u < g.num_vertices &&
		v < g.num_vertices);

	if (g.num_edges == g.edge_capacity) {
		g.edges = enlarge(4 * g.edge_capacity, 2 * g.edge_capacity, g.edges);
		g.edge_capacity *= 2;
	}

	assert(g.num_edges < g.edge_capacity);

	index_t *e = g.edges + 2 * g.num_edges;
	++g.num_edges;
	e[0] = u;
	e[1] = v;
	std::sort(e, e + 2);
}

index_t *graph_edgebuf(graph *g, index_t cap)
{
	g->edges = enlarge(2 * g->edge_capacity + 2 * cap, 2 * g->edge_capacity, g->edges);
	index_t *e = g->edges + 2 * g->num_edges;
	g->edge_capacity += cap;
	g->num_edges += cap;
	return e;
}

index_t read_graph_size(const std::string& filename)
{
	std::ifstream file(filename);
	std::string line = "";

	index_t n = 0;
	index_t m = 0;

	while (std::getline(file, line))
	{
		std::istringstream iss(line);
		char ch;

		if (iss >> ch)
		{
			if (ch == 'p')
			{
				std::string format = "";
				if (iss >> format >> n >> m)
				{
					// Format can be whatever (like "edge").
				}
				else
				{
					const std::string error = "Badly formatted problem line in " + filename;
					std::cerr << error << "\n";
					assert(false && "Badly formatted problem line");
				}
			}
		}
	}

	return n;
}

edge_set edges;

graph read_dimacs(const std::string& filename)
{
	const index_t n = read_graph_size(filename);
	std::ifstream file(filename);
	std::string line = "";

	graph g(n);

	while (std::getline(file, line))
	{
		std::istringstream iss(line);
		char ch;

		if (iss >> ch)
		{
			if (ch == 'e')
			{
				index_t u = 0;
				index_t v = 0;
				if (iss >> u >> v)
				{
					// In DIMACS, vertices start from 1 (not from 0)
					graph_add_edge(g, u - 1, v - 1);

					// Additional data structure for fast adjacency lookup
					edges.insert(std::make_pair(u - 1, v - 1));
				}
				else
				{
					const std::string error = "Badly formatted edge line in " + filename;
					std::cerr << error << "\n";
					assert(false && "Badly formatted edge line");
				}
			}
		}
	}

	return g;
}

void graph_to_adj_lists(const graph& g, index_t*& adj, index_t*& pos)
{
	std::vector<index_t> deg(g.num_vertices, 0);
	const index_t* e = g.num_edges == 0 ? 0 : &g.edges[0];

	for (index_t i = 0; i < g.num_edges; ++i)
	{
		++deg[e[0]];
		++deg[e[1]];
		e += 2;
	}

	std::vector<index_t> cumdeg;
	cumdeg.reserve(deg.size());
	std::partial_sum(deg.cbegin(), deg.cend(), std::back_inserter(cumdeg));

	const index_t totdeg = cumdeg.back();
	std::vector<index_t> adj_helper(g.num_vertices + totdeg);

	if (e)
		e = &g.edges[0] + 2 * (g.num_edges - 1);

	for (index_t i = 0; i < g.num_edges; ++i)
	{
		adj_helper[--cumdeg[e[0]]] = e[1];
		adj_helper[--cumdeg[e[1]]] = e[0];
		e -= 2;
	}

	assert(!pos && !adj);

	pos = new index_t[g.num_vertices];
	adj = new index_t[g.num_vertices + totdeg];

	auto iter = adj_helper.begin();
	auto p_it = adj_helper.begin();

	for (index_t i = 0; i < g.num_vertices; ++i)
	{
		const index_t i_deg = deg[i];

		pos[i] = std::distance(adj_helper.begin(), p_it);

		p_it += i_deg + 1;
		adj[pos[i]] = i_deg;

		std::copy(iter, iter + i_deg, adj + pos[i] + 1);
		iter += i_deg;

		assert(adj[pos[i]] == deg[i]);
	}
}

std::vector<index_t> get_adjacency_list(index_t v, index_t* adj, index_t* pos)
{
	const index_t adjpos = adj[pos[v]];
	std::vector<index_t> neigh(adjpos);

	for (int i = 0; i < adjpos; ++i)
	{
		neigh[i] = adj[pos[v] + i + 1];
	}

	return neigh;
}

bool next_combination(index_t* c, index_t n, index_t k)
{
	if (c[k - 1] < n - 1)
	{
		++c[k - 1];
		return true;
	}

	std::int64_t j;

	for (j = k - 2; j >= 0; j--)
	{
		if (c[j] < n - k + j)
		{
			break;
		}
	}

	if (j < 0)
	{
		assert(c[0] == n - k);
		return false;
	}

	++c[j];

	for (; j < k - 1; ++j)
	{
		c[j + 1] = c[j] + 1;
	}

	return true;
}

double local_clustering_coefficient(index_t v, index_t* adj, index_t* pos)
{
	const auto neigh = get_adjacency_list(v, adj, pos);
	const index_t n = neigh.size();
	const index_t k = 2;

	if (n < 2)
	{
		return 0.0;
	}

	index_t* vset = new index_t[k];
	std::iota(vset, vset + k, 0);

	index_t tr_count = 0;
	index_t total = 0;

	do
	{
		// v[0], v[1] is the index pair to check
		if (edges.find(std::make_pair(neigh[vset[0]], neigh[vset[1]])) != edges.end())
		{
			++tr_count;
		}

		++total;
	} while (next_combination(vset, n, k));

	delete[] vset;

	return tr_count / static_cast<double>(total);
}

std::vector<double> local_clustering(index_t n, index_t* adj, index_t* pos)
{
	std::vector<double> coeffs(n);
	for (int i = 0; i < n; ++i)
	{
		coeffs[i] = local_clustering_coefficient(i, adj, pos);
	}

	return coeffs;
}

int main(int argc, char *argv[])
{
	if (argc != 2)
	{
		std::cout << "Usage: ./local-coeff <filename>\n";
		return 0;
	}

	const std::string file(argv[1]);
	const index_t n = read_graph_size(file);
	graph g = read_dimacs(file);

	// auto start = std::chrono::steady_clock::now();

	index_t* adj = 0;
	index_t* pos = 0;
	graph_to_adj_lists(g, adj, pos);

	auto coeffs = local_clustering(n, adj, pos);

	// auto finish = std::chrono::steady_clock::now();
	// double elapsed_seconds = std::chrono::duration_cast<
	// 	std::chrono::duration<double> >(finish - start).count();
	// std::cout << elapsed_seconds << " s\n\n";

	std::sort(coeffs.begin(), coeffs.end());

	for (auto e : coeffs)
		std::cout << e << " ";
	std::cout << "\n";

	delete[] adj;
	delete[] pos;
}
