/*
 * This file is SATMargin.
 * This product includes software developed by XXX
 * 
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the General Public License
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * FITNESS FOR A PARTICULAR PURPOSE.  See the
 * 
 *
 * Compile: 
 * g++ -std=c++11 SATMargin.cpp -lcryptominisat5 -o SATMargin
 * Please install Cryptominisat5.1 Before your compilation
 * Please see input file example: 55221. Each line is one edge, graphs are separate by "#".
 *
 * Execute: 
 * ./SATMargin 55221
 *
 */
//Library
#include<time.h>				//System timer
#include<limits>				//test data type limit 
#include<fstream>				//fileI/O
#include<iostream>				//stdI/O
#include<iomanip>				
#include<string>		
#include<sstream>
#include<cstdlib>
#include<typeinfo>
#include<stack>
#include<list>
#include<unordered_map>
#include<vector>
#include<sys/resource.h>			//System Memory Usage
#include<stdlib.h>				//Standard Library
#include<math.h>				//Math Calculation
#include <sys/time.h>				//Timer
#include <unordered_set>
#include <algorithm>

//SAT head
#include "cryptominisat5/cryptominisat.h"
#include <cassert>

using namespace CMSat;
using namespace std;

/*
 * Edge class with edge index, vertex index and edgelabel. Can be extended to labeled graph.
 */
class Edge{
public:
	short index;
	short i;
	short j;
	short edgelabel;
	void initial(short ,short ,short ,short);
};
void Edge::initial(short index1, short i1, short j1, short edgelabel1){
	index = index1;
	i = i1;
	j = j1;
	edgelabel = edgelabel1;
}
/*
 * Graph Edge class with edge adjacency matrix and the vertex list.
 */
class Graph{
public:
	//short graphlength;
	vector<Edge> e;					//edge vector of graph
	vector<vector<short>> map;				//adjacent map
	vector<bool> vl;					//vertex list: True in graph False not in graph
	void setedges(short, short, short, short);		//set edges by class function
	void copy(Graph& g, Edge& last);			//initial by one more edge and graph
};
//set edge with edgeindex = index
void Graph::setedges(short index, short i, short j, short edgelabel){
	e[index].index = index;
	e[index].i = i;
	e[index].j = j;
	e[index].edgelabel = edgelabel;
}
void Graph::copy(Graph& g, Edge& last){
	for(short i=0; i<g.e.size(); i++){
		e.push_back(g.e[i]);		
	}
	e.push_back(last);
}
/*
 * Cut class includes two subgraphs: MFS as pl, and its infrequent child subgraph as cl. Each Cut is in the Margin space.
 * stored by as the edge list of G_min.
 * Child graph is the infrequent subgraph, Parent graph is the frequent subgraph.
 */
class Cut{
public:
	vector<short> cl;					//graph child edge list
	vector<short> pl;					//graph parent edge list
	void setcut(Graph &, short);				//set cut child and removed edge list
	void set(vector<short>& cl1, vector<short>& pl1);	//set by child and parent edgelist
};
void Cut::set(vector<short>& cl1, vector<short>& pl1){
	cl = cl1;
	pl = pl1;
}
void Cut::setcut(Graph& p, short edgeindex){
	cl.clear();
	pl.clear();	
	//update parent edge list: pl
	for(short i=0; i<p.e.size(); i++){
		pl.push_back(p.e[i].index);	
	}
	//
	//update child parent edge list: cl
	cl = pl;
	short shift=0;
	for(short i=0; i<p.e.size(); i++){
		if(p.e[i].index < edgeindex){
			shift++;	
		}	
		else{break;}
	}	
	vector<short>::iterator it;
	it = cl.begin();
	it = it + shift;
	cl.insert(it, edgeindex); 
	//
}
//>end class cut

//global var
short minsupport =1;				//minimum support for a pattern
short graphnum = 0;			
vector<Graph> G;				//graph dataset
short nedgelabel =4;				//number of edgelabel in this edgelabel system
vector<short> representpath;			//representative path from G[min] to a representative
short minindex;				//index of smallest graph in G as G_min
unordered_map<string, bool> hashmap;		//hashkey of explored cuts
double lowerenergy = 0.5;			//metropolis criterial
double equalenergy = 0.8;			//metropolis criterial

long int step =0;				//count steps used
clock_t global_start;				//global clock
clock_t global_end;
long int current_largest_sub = 0;		//current largest length subgraph found
string filename = "";				//graph.data.set filename
string cutfilename = "";			//current MFS filename for second round search
short cut_read_in_flag;			//If read initial MFS from file 

double iso_usage = 0;				//isomophism time usage
unsigned int iso_num = 0;			//number of isomophism used
unsigned int nextcutratio = 10;		//The ratio of next cut
unsigned int count_edge_mapping = 0;          //count number of edge mapping for performance
unsigned int decision = 0;                    //number of literal assignment


vector<vector<int>> last_result;		//assumptions assignment from last SAT test in G[0] G[1] G[2]
vector<Graph> last_subgraph;			//last subgraph list queried by each graph     G[0] G[1] G[2]
vector<bool> has_last_subgraph;		//bool to make sure has last subgraph query, with SATSI == 1
int curr_graph_index = -1;			//curr graph of SATSI


//Functions Declarationm. General helper functions are not listed.
/******************************************************************************************************
initialization and readin graphs
******************************************************************************************************/
void initialization();
void loadGraphs();
/******************************************************************************************************
Debug output functions
******************************************************************************************************/
void outputmemoryusage();			//Print memory useage
void outputsinglegraph(Graph &);		//Print a graph
void outputsingleedge(Edge &);		//Print an edge
void outputmap(Graph &);			//Print adjacency matrix
void outputvl(Graph &);			//Print vertex list
void outputgraph(Graph &);			//Print graphs
void outputrepath();				//Print the order of edge removal to find initial MFS
void outputvector(vector<short>&);		//Print general short vector
void outputvector(vector<bool>&);		//Print general Boolean vector
void outputcut(Cut&);				//Print MFS and it direct infrequent child (one more edge)
void outputstackusage(stack<Cut> cutstack);	//Print stack usage for complete Margin
/******************************************************************************************************
Memory usage functions
******************************************************************************************************/
static string memory_usage();
/******************************************************************************************************
Subgraph search: find representative
******************************************************************************************************/
short removeedge(Graph &g);			//remove one edge from g
short connectivity(Graph&);			//if connected graph
short findlargestvertex(Graph&); 		//find largest vertex in graph
void  adjacent(Graph &);			//update adjacent map in Graph 
short support(Graph& sub);			//find support of sub in G[], return support
bool  notused(short j, vector<short>);	//check if vertex used in stmp
short nextvertex(vector<short>, Graph);	//find next candidate for isomorphism to add one vertex in stmp
vector<short> mapnextvertex(short, vector<short>, vector<short>, Graph, Graph );
						//find a next vertex in Graph g which map to vertex nexts in Graph s
short isomorphism(Graph sub, Graph g);	//find sub isomorphism of sub in graph g
short smallestgraph();				//find smallest graph
Graph findrepresentative();			//find representative 
Cut loadrepresentative();			//Load initial MFS from file, not using
void savecutfile(Cut &cut);			//Save current MFS file for future use popose 
/******************************************************************************************************
Subgraph search: Functions to Find MFS and its neighbors
******************************************************************************************************/
short support(vector<short>& el);								//Determine the frequency of a subgraph by edge list el, or edgelist el are indexed by G_min graph
short connectivity(vector<short>& el);							//Determine the connectivity of a subgraph by edge list el
Graph el2graph(vector<short> el);								//Convert subgraph edge list to Graph instance 
bool vectorequal(vector<short>& v1, vector<short>& v2);					//Compare if two vector is equal
void onelessedge(vector<vector<short>>& re, vector<short>& cl, vector<short>& pl);		//Remove one edge from edge list pl to find smaller subgraph
short elcomparation(vector<short>& el1, vector<short>& el2);					//Add one edge from edge list pl to find larger subgraph
void onemoreedge(vector<vector<short>>& call, vector<short>& pi, vector<short>& cl);	//Add one edge from edge list pl to find larger subgraph
vector<short> commonparent(vector<short>& cl1, vector<short>& cl2);				//Construct the commmon parent of two subgraph which has two edge difference
void firstonelessedge(vector<short>& re, vector<short>& cl);					//Construct one less edge from edge list cl
void set_hash_key(vector<short>& curr);							//Set hashkey for current MFS, complete Margin 
bool get_hash_key(vector<short>& curr);							//Find if current MFS is in hash table.
void clear_hash_key();										//Clear all hash keys
void expandcut(Cut&);										//Random Walk in the Margin space
/******************************************************************************************************
Monte Carlo Random
******************************************************************************************************/
void random_onelessedge(vector<short>& cl, vector<short>& pl);				//Find one less edge subgraph randomly 
void random_onemoreedge(vector<short>& ci, vector<short>& pi);				//Find one more edge subgraph randomly

Cut get_type_pall(Cut& curr);									//Choose new subgraph by pl edge list
Cut get_type_call(Cut& curr);									//Choose new subgraph by cl edge list
Cut get_type_m(Cut& curr);									//Choose one more edge new subgraph 
Cut get_type_s1(Cut& curr);									//Choose one less edge new subgraph

Cut get_next_cut(Cut& curr);									//Find next cut to for Random Walk
short metropolis(short enew, short eold);							//MCMC
short metropolis_1(short enew, short eold);							//MCMC_old
/******************************************************************************************************
SAT Solver to determine subgraph monomorphism
******************************************************************************************************/
short 	SATSI(Graph& s, Graph& g);								//SAT Subgraph Monomorphism
vector<Lit> identify_same_vertex(Graph &s1, Graph &s2, Graph & g);				//Identify the shared vertex literal from last SATSI call 
lbool SATSI_without_opt(Graph& s, Graph& g);							//SAT Subgraph Monomorphism without neighboring subgraph common literal sharing 
/******************************************************************************************************
initialization and readin graphs
******************************************************************************************************/
/*
 *initialize global values
 */
void initialization(){
	
	equalenergy = 0.8; 				// Acceptance ratio of equal sized subgraphs
	lowerenergy = 0.5;				// Acceptance ratio of smaller sized subgraphs

	cutfilename = "";				// For read cut from file
	cut_read_in_flag = 0;
	nextcutratio = 10;
	
	srand((unsigned)time(0));			//random seeds
	srand(rand());					//random seeds
        
        clear_hash_key();				//Hash_key is for completely search of MFS neighrbors 
	step = 0;					//Iteration steps
	return ;
}
/*
 * Load input graph files to G vector, which includes all input graphs
 */
void loadGraphs(){
	string line;
	ifstream graphdata(filename);

	Graph gg;
	gg.e.clear();
	Edge ee;

	short j = 0;
	short gl = -1;  					//graph length index
	short gn = 0; 						//graphs number index
	short index, ver1, ver2 , edg; 			//Set edge label
	//read each edge line
	while(graphdata >> line){	
		if(line.compare("@") == 0){			//edge separator
			j = 0;
			gl++;
		}
		if(line.compare("#") == 0){			//graph separator
			G.push_back(gg);			//push ot G vector
			gg.e.clear();
			gl = -1;
			gn++;
		}
		// read each edge
		if(line.compare("@") != 0 && line.compare("#") != 0){
			if(j==0){istringstream(line)>>index;}
			if(j==1){istringstream(line)>>ver1;}
			if(j==2){istringstream(line)>>ver2;}
			if(j==3){
				istringstream(line)>>edg;
				ee.initial(gl, ver1,ver2,edg);
				gg.e.push_back(ee);
			}
			j++;
		}
	}
	graphdata.close();
	graphnum = gn;
	
	//update the adjacent map of each input graph
	for(short i =0; i<G.size(); i++){
		adjacent(G[i]);
	}
	
	//Prepare for hash table, used in complete Margin
	for(short i=0; i<G.size(); i++){
		last_subgraph.push_back(G[i]);
		vector<int> curr {-1};
		last_result.push_back(curr);
		has_last_subgraph.push_back(false);
	}
	
	return ;
	
}
/******************************************************************************************************
output functions for debug
******************************************************************************************************/
/*
 * Print graph
 */
void outputsinglegraph(Graph &g){
	//cout<<"  length = "<<g.e.size()<<endl;
	for(short i = 0; i< g.e.size(); i++){
		cout<<"("<<g.e[i].i<<","<<g.e[i].j<<")";
	}cout<<endl;
	return ;
}
/*
 * Print memory usage
 */
void outputmemoryusage(){
	cout<<"Current memory usage is : "<<memory_usage()<<endl;
	return ;
}
/*
 * Print edge
 */
void outputsingleedge(Edge & e){
	cout<<"Edge:"<<e.index<<" "<<e.i<<" "<<e.j<<" "<<e.edgelabel<<endl;
	return ;
}
/*
 * Print adjacency matrix 
 */
void outputmap(Graph &g){
	cout<<setw(4)<<" ";
	for(short i=0; i<g.map.size(); i++){
		cout<<setw(4)<<i;
	}cout<<endl;
	for(short i=0; i<g.map.size(); i++){
		cout<<setw(4)<<i;
		for(short j=0; j<g.map[i].size(); j++){
			cout<<setw(4)<<g.map[i][j];
		}cout<<endl;
	}
	return;
}
/*
 * Print vertex list of graph
 */
void outputvl(Graph &g){
	for(short i=0; i<g.vl.size(); i++){
		cout<<g.vl[i]<<" ";
	}cout<<endl;
	return ;
}
/*
 * Print graph
 */
void outputgraph(Graph &g){
	cout<<"<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<"<<endl;
	cout<<"graph:"<<endl;
	outputsinglegraph(g);
	cout<<"map:"<<endl;
	outputmap(g);
	cout<<"vertex list:"<<endl;
	outputvl(g);
	cout<<">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>"<<endl;
	return ;
}
/*
 * Print path to remove edge to find initial MFS
 */
void outputrepath(){
	cout<<"Path to representative:"<<endl;	
	for(short i=0; i<representpath.size(); i++){
		cout<<representpath[i]<<" ";
	}cout<<endl;
	return ;
}
/*
 * Print general vector
 */
void outputvector(vector<short>& ve){
	for(short i=0; i<ve.size(); i++){
		cout<<setw(4)<<ve[i];
	}cout<<endl;
	return ;
}
/*
 * Print matrix
 */
void outputvectorvector(vector<bool>& ve){
	for(short i=0; i<ve.size(); i++){
		cout<<setw(4)<<ve[i];
	}cout<<endl;
	return ;
}
/*
 * Print MFS (pl) and its infrequent child subgraph (cl) by edge list of G_min
 */
void outputcut(Cut& c){
	cout<<"<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<"<<endl;
	cout<<"Child: ";
	outputvector(c.cl);
	cout<<"Parent:";
	outputvector(c.pl);
	cout<<">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>"<<endl;
	return ;
}
/*
 * print stack usage
 */
void outputstackusage(stack<Cut> cutstack){
	cout<<"Stack size: "<<cutstack.size()<<endl;
	return ;
}
/*
 * Output the chosen move type of chosen neibghbor MFS
 */
void outputmovetype(short t){
	if(t == 0){
		cout<<"\r     ";		
		cout.flush();		
		cout<<"\rpall";
		cout.flush();		
	}
	if(t == 1){
		cout<<"\r     ";		
		cout.flush();		
		cout<<"\rcall";
		cout.flush();		
	}
	if(t == 2){
		cout<<"\r     ";		
		cout.flush();		
		cout<<"\rM";
		cout.flush();		
	}
	if(t == 3){
		cout<<"\r     ";		
		cout.flush();		
		cout<<"\rs1";
		cout.flush();		
	}
	return ;
}
/******************************************************************************************************
Memory usage functions
******************************************************************************************************/
/*
 * Get memory usage of current proc
 */
static string memory_usage(){
        ostringstream mem;
        ifstream proc("/proc/self/status");
        string s;
        while(getline(proc, s), !proc.fail()) {
                if(s.substr(0, 6) == "VmSize") {
                        mem << s;
                        return mem.str();
                }
        }
        return mem.str();
}
/******************************************************************************************************
Subgraph search: find representative
******************************************************************************************************/
/*
 * Choose one edge from Graph g, return the removed edge's edgeindex in G[min], return edge index of graph to remove
 */
short removeedge(Graph &g){
	short graphlength = g.e.size();
	srand((unsigned)time(0)); 				//random seed
	short connect = 0;
	Graph tmp = g;						//backup graph g for restore
	short edgeindex = -1;					//removed edgeindex in G[min]
	while(connect == 0 || connect == -1){
		short index;		
		index = rand()%graphlength;			//generate random number from 0 to graphlength-1	
		edgeindex = g.e[index].index;		
		g.e.erase(g.e.begin()+index);			//remove one edge
		adjacent(g);					//update adjacent map
		connect = connectivity(g);
		if(connect == 0 || connect == -1){		//restore original g
			g = tmp;
		}
	}
	return edgeindex;
}
/*
 * Graph connectivity test: if a connected graph return 1 when connected 0 when not connected -1 when NULL graph
 */
short connectivity(Graph& g){

	if(g.map.size() == 0)
		return -1;
	
	vector<bool> connection;
	for(short i=0; i<g.map.size(); i++){	//initial
		connection.push_back(false);
	}

	stack<short> vstack;			//vertex index 
						//loop over graph edges and check vertex list is complete
	short entrypoint;			//Apply vl to choose entry point
	for(short i=0; i<g.vl.size(); i++){
		if(g.vl[i] == true){
			entrypoint = i;
			break;	
		}
	}
	
	vstack.push(entrypoint);
	connection[entrypoint] = true;
	while(!vstack.empty()){
		short i = vstack.top();
		vstack.pop();
		for(short j=0; j<g.map[i].size(); j++){
			if(g.map[i][j] != -1){
				//cout<<i<<j<<endl;
				if(connection[j] == false){
					vstack.push(j);
					connection[j] = true;
				}			
			}
		}
	}

	for(short i=0; i<connection.size(); i++){
		if(connection[i] == false && g.vl[i] == true){
			return 0;			
		}
	}
	return 1;
}
/*
 * Find the index of largest vertex in graph g
 */
//<find largest vertex in graph
short findlargestvertex(Graph & g){
	short tmp = 0;
	for(short i = 0; i < g.e.size(); i++){
		if(g.e[i].i > tmp){tmp = g.e[i].i;}
		if(g.e[i].j > tmp){tmp = g.e[i].j;}
	}
	return tmp;
}
/*
 * Construct adjacency map of graph g, load into g.map
 */
void adjacent(Graph &g){			//update adjacent map in Graph
	g.map.clear();				//clear map
	g.vl.clear();				//clear vertex list

	short vm = findlargestvertex(g);

	for(short i=0; i<=vm; i++){		//initial vl map
		g.map.push_back(vector<short>());
		g.vl.push_back(false);
		for(short j=0; j<=vm; j++){
			g.map[i].push_back(-1);
		}
	}

	for(short i=0; i<g.e.size(); i++){
		g.map[g.e[i].i][g.e[i].j] = g.e[i].edgelabel;
		g.map[g.e[i].j][g.e[i].i] = g.e[i].edgelabel;
		if(g.vl[g.e[i].i] == false){g.vl[g.e[i].i] = true;}
		if(g.vl[g.e[i].j] == false){g.vl[g.e[i].j] = true;}
	}

	return ;
}

/*
 * Find the frequency of a subgrph among input graphs
 */
short support(Graph& sub){
	short sup = 0;
	for(short i=0; i<G.size(); i++){
		if(i != minindex){//skip G[min] 
			
			count_edge_mapping = 0;
			clock_t ss1 = clock();
			
			//update current graph index
			curr_graph_index = i; 			//Update curr G in SATSI for vector to store last subgraphs and last vertex mapping literals
			
			clock_t ss = clock();
			
			short	satiso = SATSI(sub, G[i]); 	//Compute the frequency by SAT subgraph monomorphism 
			
			clock_t ee = clock();
			
			double time1 = (double)(ee - ss)/CLOCKS_PER_SEC;
			
			cout<<" "<<time1<<" "<<sub.e.size()<<endl;
			
			sup += satiso;				//aggregate support
			
			clock_t ee1 = clock();
			double time2 = (double)(ee1 - ss1)/CLOCKS_PER_SEC;

			decision = 0;
		}
	}
	sup++;//add frequency of G[min]
	
	return sup;
}
/*
 * Vertex j is not used in vertex list stmp 
 * return: true if not used, false if used
 */
bool notused(short j, vector<short> stmp){
	for(short i=0; i<stmp.size(); i++){
		if(j == stmp[i]){
			return false;
		}
	}
	return true;
}
/*
 * Find candidate next vertex to extend subgraph
 * Return the vertex number or -1 if impossible
 */
short nextvertex(vector<short>stmp, Graph s){
	short next;
	for(short i=0; i<stmp.size(); i++){
		for(short j=0; j<s.map[stmp[i]].size(); j++){
			if(s.map[stmp[i]][j] != -1){
				if(notused(j, stmp)){
					return j;
				}			
			}
		}
	}
	return -1;
}
/*
 * Map one next vertex in g as candidate to nexts that connected with vertices in gtmp
 * Return candidate of next vertex in g 
 */
vector<short> mapnextvertex(short nexts, vector<short> stmp,vector<short> gtmp,Graph s, Graph g){
        vector<short> cand;
        									//update used (gtmp) verteices in g     
        vector<bool> used;
        for(short i=0; i<g.map.size(); i++){
                used.push_back(false);
        }
        for(short i=0; i<gtmp.size(); i++){
                used[gtmp[i]] = true;   
        }
        
        for(short i=0; i<g.map.size(); i++){					//for all vertex in g
                if(used[i] == false){						//not previously used in gtmp
                        short flag = 1;
                        for(short j=0; j<stmp.size(); j++){			//all used vertex in stmp
                                if(s.map[nexts][stmp[j]] != -1){		//stmp[j] connected with nexts
                                        
					count_edge_mapping++;			//count number of edge mapping for statitic

                                        if(s.map[nexts][stmp[j]] != g.map[i][gtmp[j]]){
                                                flag = -1;
                                                break;
                                        }
                                }
                        }
                        if(flag == 1){
                                cand.push_back(i);              
                        }
                }       
        }
        return cand;
}
/*
 * Original non-induced isomorphism between subgraph sub and graph g
 * Return 1 when has mapping, 0 when none.
 * Replaced by SATSI
 */

short isomorphism(Graph s, Graph g){
        iso_num++;
	clock_t iso_s = clock();			//add timer start	
	clock_t iso_e;
	//get length of vertex list in s
	short svlength=0;
	for(short i=0; i<s.vl.size(); i++){
		if(s.vl[i] == true){
			svlength++;
		}
	}
	//stack	
	stack<vector<short>> sstack;			//sub vertex map stack
	stack<vector<short>> gstack;			//g   vertex map stack
	stack<short>         lstack;			//vertexlength stack
	//map first vertex in sub to g

	vector<short> sone;				//vertex map in sub
	vector<short> gone;				//vertex map in g	
	short i=0; 
	while(s.vl[i] == false){
		i++;	
	}
	sone.push_back(i);				//add first vertex in subone
	for(short i=g.vl.size()-1; i>=0; i--){	//add possible vertex in g as map of first vertex in subone
		gone.push_back(i);		
		sstack.push(sone);			//add to submap stack
		gstack.push(gone);			//add to gmap stack
		lstack.push(1);
		gone.pop_back();			//pop and prepare for next gone.push_back()
	}
	while(!sstack.empty()){
		//get map result of n-1 stmp list		
		vector<short> stmp = sstack.top();
		vector<short> gtmp = gstack.top();
		short vlength      = lstack.top();	
		
		sstack.pop();
		gstack.pop();
		lstack.pop();
		
		//Identify the mapping between s and g 		
		if(vlength == svlength){
			iso_e = clock();					    		//add timer end
			iso_usage = iso_usage + (double)(iso_e-iso_s)/CLOCKS_PER_SEC;	//add time usage to total		
			return 1;
		}
		short nexts = nextvertex(stmp, s);						//get next candidate vertex add to stmp
		vector<short> nextg = mapnextvertex(nexts, stmp, gtmp, s, g);		//Find all vertex in g which map to nexts
		
												//prepare stmp, gtmp and vlength then push into stack
		stmp.push_back(nexts);								//Send candidate in vertex list of stmp		
		vlength++;									//add one vetertex for push into lstack		
		for(short i = nextg.size()-1; i>= 0; i--){		
						
			gtmp.push_back(nextg[i]);						//put candidate in vertex list of gtmp
						
			sstack.push(stmp);
			gstack.push(gtmp);
			lstack.push(vlength);
			
			gtmp.pop_back();
		}
		
	}
	iso_e = clock();				    					//add timer end
	iso_usage = iso_usage + (double)(iso_e-iso_s)/CLOCKS_PER_SEC;			//add time usage to total
	return 0;
}
/*
 * Find smallest graph among input graphs,
 * return index of smallest graph in global short min 
 */
short smallestgraph(){
	short minsize = G[0].e.size();		//inital number of edge in smallest graph			
	short index = 0;				//intial smallest graph index
	for(short i = 1; i<G.size(); i++){
		if(minsize > G[i].e.size()){
			index = i;
			minsize = G[i].e.size();
		}
	}
	return index;
}
/*
 * Find the initial MFS by reducing edges from G_min
 */

//end smallestgraph
Graph findrepresentative(){
	minindex = smallestgraph();
	Graph re = G[minindex];
	while(support(re) < G.size()){
		//cout<<re.e.size()<<endl;
		representpath.push_back(removeedge(re));
	}
	return re;
}
/*
 * Load intial MFS: pl and its infrequent child subgraph: cl as cut from file, that can be save for future random walk
 */
Cut loadrepresentative(){
	ifstream cutdata(cutfilename);
	Cut currcut;							//curr cut to right in
   	short cpflag = 0;						//child parent flag 1: read in child 2: read in parent
	string letter;
	short currnum = 0;						//current number
	while(cutdata >> letter){
		if(letter.compare("@") == 0){cpflag++;continue;}		//new line
		if(cpflag == 1){
			istringstream(letter) >> currnum;
			currcut.cl.push_back(currnum);
		}
		if(cpflag == 2){
			istringstream(letter) >> currnum;
			currcut.pl.push_back(currnum);
		}
	}
	return currcut;
}
/*
 * Save current cut to file for future random walk
 */
void savecutfile(Cut &cut){
	ofstream cutdata(cutfilename);
	cutdata<<"@";
	for(short i=0; i<cut.cl.size(); i++){
		cutdata<<setw(8)<<cut.cl[i];
	}
	cutdata<<endl;
	cutdata<<"@";
	for(short i=0; i<cut.pl.size(); i++){
		cutdata<<setw(8)<<cut.pl[i];
	}
}
/******************************************************************************************************
Find Neibhgor MFS: 
******************************************************************************************************/
/*
 * count support by edgelist of a subgraph
 */
short support(vector<short>& el){
	if(connectivity(el) == 0 || el.size()<= 1){		// must be connectted
		return 0;
	}
	Graph curr = el2graph(el);				//convert to edgelist to graph
	return support(curr);
}
/*
 * identify the connectivity of edgelist in G_min
 * Return 0 not connected, 1 as connected
 */
short connectivity(vector<short>& el){
	Graph curr = el2graph(el);
	return connectivity(curr);
}
/*
 * Convert subgraph edgelist of G_min to subgraph
 */
Graph el2graph(vector<short> el){
	Graph g;
	for(short i=0; i<el.size(); i++){
		g.e.push_back(G[minindex].e[el[i]]);
	}
	adjacent(g);
	return g;
}
/*
 * if two vector equal, return true when equal false when not equal
 */
bool vectorequal(vector<short>& v1, vector<short>& v2){
	for(short i=0; i<v1.size(); i++){
		if(v1[i] != v2[i]){return false;}
	}
	return true;
}
/*
 * Remove one edge from cl, return all connected one less edge graph as candidate edgelist which is not same to pl
 * This is to find a neighbor subgraph
 */
void onelessedge(vector<vector<short>>& re, vector<short>& cl, vector<short>& pl){
	vector<short> curr;	
	re.clear();	
	//choose ith edge	
	for(short i=0; i<cl.size(); i++){
		curr = cl;
		curr.erase(curr.begin() + i);
		if(connectivity(curr) == 1){
			re.push_back(curr);
		}
	}
}
/*
 * Remove edges from G_min to find the initial MFS, re stores the sequence of edges removed from G_min 
 */
void firstonelessedge(vector<short>& re, vector<short>& cl){
	for(short i=0; i<cl.size(); i++){
		re = cl;
		re.erase(re.begin() + i);
		if(support(re) == G.size()){			//frequency
			return;	
		}
	}
	re.clear();
}
/*
 * Compare edgelist  return 1 when equal, 0 when not equal
 */
short elcomparation(vector<short>& el1, vector<short>& el2){
	for(short i=0; i<el1.size(); i++){
		if(el1[i] != el2[i]){
			return 0;
		}
	}
	return 1;
}
/*
 * Get candidates of one more edge subgraph edgelist of pi except cl, first parameter is edgelist vector
 * call stores all candidate edges for neighbor MFS
 */
void onemoreedge(vector<vector<short>>& call, vector<short>& pi, vector<short>& cl){ 
	vector<short> curr;	 				//single child edgelist
	call.clear();
	for(short i=0; i<G[minindex].e.size(); i++){
		if(notused(G[minindex].e[i].index, pi)){	
			short index = G[minindex].e[i].index;
			curr.clear();
			curr = pi;
			short shift = 0;
			while(pi[shift]<index && shift< pi.size()){
				shift++;
			}
			curr.insert(curr.begin()+shift, index);
			if(connectivity(curr) == 1){		
				call.push_back(curr);		//return edgelist of currg
			}
		}
	}
}
/*
 * Given two subgraph cl1 and cl2 with one edge difference, return edgelist their common subgraph
 */
vector<short> commonparent(vector<short>& cl1, vector<short>& cl2){
	vector<short> re;						//store common parent edgelist
	for(short i=0; i<cl1.size(); i++){
		if(cl1[i] < cl2[i]){
			re = cl2;
			re.insert(re.begin()+i, cl1[i]);
			break;
		}
		if(cl1[i] > cl2[i]){
			re = cl1;
			re.insert(re.begin()+i, cl2[i]);
			break;
		}
	}
	return re;
}
/*
 * Set hash key of curr cut in hashtable, for complete search usage
 */
void set_hash_key(Cut& curr){
	string skey;
	ostringstream convertcurr;
	for(short i=0; i<curr.cl.size(); i++){
		convertcurr<<curr.cl[i]<<",";
	}
	convertcurr<<"@";
	for(short i=0; i<curr.pl.size(); i++){
		convertcurr<<curr.pl[i]<<",";
	}
	skey = convertcurr.str();
	unordered_map<string,bool>::const_iterator got = hashmap.find(skey);
	if(got == hashmap.end()){
		hashmap.insert({skey,1});
	}
}
/*
 * Test if exists hash key of current cut: find if cut is in hash table return 1 when has this key, 0 when no such key
 */
bool get_hash_key(Cut& curr){
	string skey;
	ostringstream convertcurr;
	for(short i=0; i<curr.cl.size(); i++){
		convertcurr<<curr.cl[i]<<",";
	}
	convertcurr<<"@";
	for(short i=0; i<curr.pl.size(); i++){
		convertcurr<<curr.pl[i]<<",";
	}
	skey = convertcurr.str();
	//cout<<skey<<endl;
	unordered_map<string,bool>::const_iterator got = hashmap.find(skey);
	if(got != hashmap.end()){
		//cout<<"1";
		return 1;
	}
	else{
		//cout<<"0";
		return 0;
	}
}
/*
 * Clear hash key: clear all cuts in hash table, only for monte carlo random 
 */
void clear_hash_key(){
	hashmap.clear();
}
/*
 * Given an initial Cut, random walk to explore Margin space, you can output the current cut in each random step in this function
 */
void expandcut(Cut& initial){
	stack<Cut> cutstack;
	cutstack.push(initial);

	//Timer	
	timeval t1, t2;
	double elapsedTime;
        
	while(!cutstack.empty() ){//cutstack only has one cut as the current random walk step

		gettimeofday(&t1, NULL);
		step++;	

		Cut curr = cutstack.top();
		cutstack.pop();

		if(current_largest_sub < curr.pl.size()){
			current_largest_sub = curr.pl.size();					//current largest fre subgraph length	
		}	
		
		cutstack.push(get_next_cut(curr));						//set next step's cut//choose next cut type by random
												//accept 1 or reject 0 a new cut step or return a NULL cut		
		while(cutstack.top().cl.size() == 0 
		|| cutstack.top().pl.size() == 0
		|| metropolis_1(cutstack.top().pl.size(),curr.pl.size()) == 0){			
				
				cutstack.pop();				
				cutstack.push(get_next_cut(curr));
							
		}

		gettimeofday(&t2, NULL);
		
		elapsedTime = (t2.tv_sec - t1.tv_sec) * 1000.0;
		elapsedTime += (t2.tv_usec - t1.tv_usec) / 1000.0;   		
	}
}
/******************************************************************************************************
Monte Carlo Random
******************************************************************************************************/
/*
 * random one less edge: remove one edge in cl to build pl, return is in pl
 */
void random_onelessedge(vector<short>& cl, vector<short>& pl){
	short index = rand()%(cl.size());
	pl = cl;	
	pl.erase(pl.begin() + index);
	
	return ;
}
/*
 * random one more edge: add one edge in pi  to build ci, return in ci
 */
void random_onemoreedge(vector<short>& ci, vector<short>& pi){ 
	ci = pi;	

	short edgeindex = rand()%(G[minindex].e.size());
	while(!notused(G[minindex].e[edgeindex].index, pi)){
		edgeindex = rand()%(G[minindex].e.size());
	}
	
	short index = G[minindex].e[edgeindex].index;
	short shift = 0;
	while(pi[shift]<index && shift< pi.size()){
		shift++;
	}
	
	ci.insert(ci.begin()+shift, index);
	
	return ;
}
/*
 * get type 0(pall) next cut
 */
Cut get_type_pall(Cut& curr){
	Cut re;
	re.cl = curr.cl;
	random_onelessedge(re.cl, re.pl);
	short count = 0;
	while(support(re.pl) < G.size() && count <= G[minindex].e.size()){		//support test includes connectivity test
		count++;								//break while loop
		
		re.cl = curr.cl;		
		random_onelessedge(re.cl, re.pl); 
		
	}
	if(count > G[minindex].e.size()){Cut null;null.pl.clear();null.cl.clear();return null;}		//did not find new cut
	return re;
}
/*
 * get type 1(call) next cut
 */
Cut get_type_call(Cut& curr){
	Cut re;
	Cut pall = get_type_pall(curr);

	if(pall.pl.size() == 0){Cut null;null.pl.clear();null.cl.clear();return null;}	//did not find any pall
	re.pl = pall.pl;
	random_onemoreedge(re.cl, re.pl);
	short count = 0;

	while(support(re.cl) == G.size() && count <= G[minindex].e.size()){		
		count++;

		pall = get_type_pall(curr);
		re.pl = pall.pl;
		random_onemoreedge(re.cl, re.pl);
	}
	if(count > G[minindex].e.size()){Cut null;null.pl.clear();null.cl.clear();return null;}		//did not find new cut
	return re;
}
/*
 * Get type 2 next cut
 */
Cut get_type_m(Cut & curr){
	Cut re;
	Cut pall = get_type_pall(curr);

	if(pall.pl.size() == 0){Cut null;null.pl.clear();null.cl.clear();return null;}			//did not find any pall	
	re.pl = pall.pl;
	random_onemoreedge(re.cl, re.pl);
	short count = 0;

	while(support(re.cl) < G.size() && count <= G[minindex].e.size()){		
		count++;
		re.pl = pall.pl;
		random_onemoreedge(re.cl, re.pl);
	}
	if(count > G[minindex].e.size()){Cut null;null.pl.clear();null.cl.clear();return null;}		//did not find new cut	
	vector<short> m = commonparent(re.cl, curr.cl);

	re.pl = re.cl;	
	re.cl = m;
	return re;
}
/*
 * get type 3 next cut s1
 */
Cut get_type_s1(Cut & curr){
	Cut re;
	re.cl = curr.cl;
	random_onelessedge(re.cl, re.pl);
	short count = 0;
	while(support(re.pl) == G.size() && count <= G[minindex].e.size()){		//support test includes connectivity test	
		count++;				

		re.cl = curr.cl;		
		random_onelessedge(re.cl, re.pl);
	}
	if(count > G[minindex].e.size()){Cut null;null.pl.clear();null.cl.clear();return null;}		//did not find new cut	
	re.cl = re.pl;
	firstonelessedge(re.pl, re.cl);
	if(re.pl.size() == 0){Cut null;null.pl.clear();null.cl.clear();return null;}		//did not find new cut
	return re;
}
/*
 * add edge to pi subgraph to find a frequent subgraph
 */

void random_replaceedge(vector<short>& ci, vector<short>& pi){ 
        vector<short> ptmp = pi;
        int i = 6;
        while(i>0){
                i--;
                short edgeindex = rand()%(G[minindex].e.size());
                while(!notused(G[minindex].e[edgeindex].index, ptmp)){
                        edgeindex = rand()%(G[minindex].e.size());
                }

                short index = G[minindex].e[edgeindex].index;
                short shift = 0;

                while(ptmp[shift]<index && shift< ptmp.size()){
                        shift++;
                }
                ptmp.insert(ptmp.begin()+shift, index);

                if(support(ptmp) == G.size()){
                        pi = ptmp;
                }
                else{break;}
        }
        ci = pi;
        while(support(ci)==G.size()){
                ci = pi;
                short edgeindex = rand()%(G[minindex].e.size());
                while(!notused(G[minindex].e[edgeindex].index, ci)){
                        edgeindex = rand()%(G[minindex].e.size());
                }
                short index = G[minindex].e[edgeindex].index;
                short shift = 0;
                while(ci[shift]<index && shift< ci.size()){
                        shift++;
                }
                ci.insert(ci.begin()+shift, index);
        }
}
/*
 * Choose neighbor MFS in random walk
 */
Cut get_type_global(Cut & curr){
	Cut re;

	re.pl = curr.pl;
	re.cl = curr.cl;		
	
	random_replaceedge(re.cl, re.pl);
	
	return re;
}
/*
 * Choose the next cut
 */
Cut get_next_cut(Cut& curr){
	short cut_type = rand()%nextcutratio;				//4 types of cut: pall, call, m and s1
	Cut re;							//next cut
	
	if(cut_type >= 4){						
		re = get_type_global(curr);	
	}	
	if(cut_type == 0){
		re = get_type_pall(curr);
	}
	if(cut_type == 1){
		re = get_type_call(curr);
	}
	if(cut_type == 2){
		re = get_type_m(curr);
	}
	if(cut_type == 3){
		re = get_type_s1(curr);
	}

	return re;
}
/*
 * metropolis criterion to accept newly generated cut 
 * parameter: generated random number vs exp(deltaE/KT) (first version for try), short temperature is T here
 * return: 0 not accept new cut, 1 accept new cut
 */

short metropolis(short enew, short eold){
	double K = 1.0;
	double temperature = 1.0;
	double r_num = 1.0;					//random number in [0, 1]	
	
	//generate random number
	r_num = (double)rand()/(RAND_MAX);
	
	double m_value = 0.0;					//metropolis criterion value to compare with random number
	m_value = exp((enew-eold)/(K*temperature));
	
	if(r_num <= m_value){
				
		return 1;
	}
	else{
		return 0;	
	}
	
}
/*
 * Old 
 * metropolis_1: metropolis by assigned probability
 * return: 0 not accept new cut, 1 accept new cut
 */

short metropolis_1(short enew, short eold){
	if(enew > eold){
		return 1;
	}
	if(enew == eold){
		double r_num = 0.0;
		r_num = (double)rand()/(RAND_MAX);
		if(r_num <= equalenergy){
			return 1;
		}
		else{
			return 0;		
		}
	}
	if(enew < eold){
		double r_num = 0.0;
		r_num = (double)rand()/(RAND_MAX);
		if(r_num <= lowerenergy){
			return 1;
		}

		else{
			return 0;		
		}
	}
	return 0;
}
/******************************************************************************************************
SAT SI
******************************************************************************************************/
typedef long long ll;
/*
 * Convert vertex pair ij to a index (n2*j + i + 1)-1;
 */
ll getvarno(ll n2, ll j, ll i)
{
	return (n2*j + i + 1)-1;
}
/*
 * Pair of vertex in hash table
 */
struct pairhash {
public:
  template <typename T, typename U>
  std::size_t operator()(const std::pair<T, U> &x) const
  {
    return std::hash<T>()(x.first) ^ std::hash<U>()(x.second);
  }
};
/*
 *
 */
void outputmap(unordered_map<ll,ll> &curr){
	cout<<"graph"<<endl;
	for(auto c:curr){
		cout<<c.first<<" "<<c.second<<endl;
	}
	cout<<endl;
	return;
}
/*
 * output graph as ll type
 */
void outputlongmatrix(std::vector<std::vector<ll>> & G1){
	for(auto GG : G1){
		for(auto G : GG){
			cout<<G<<" ";
		}cout<<endl;
	}
	cout<<endl;
	return;
}
/*
 * Original SAT subgraph monomorphism function without neighbor MFS mapping assistant. Out of date
 */
lbool SATSI_without_opt(Graph& s, Graph& g){	
		return l_True;
}
/*
 * Identify same vertex between subgraphs s1 and s2, by the order in SAT solver: to build new_assumptions  
 */
vector<Lit> identify_same_vertex(Graph &s1, Graph &s2, Graph & g){
		std::unordered_map<ll,ll> N1; // s1
		std::unordered_map<ll,ll> N2; // s2
		std::unordered_map<ll,ll> N3; // g


		std::vector<std::pair<ll,ll> > SN1;
		std::vector<std::pair<ll,ll> > SN2;
		vector<ll> edgelabel1;
		vector<ll> edgelabel2;
	
		int j = 1;

		for(short i = 0; i< s1.e.size(); i++){
			ll x1 = s1.e[i].i;
			ll x2 = s1.e[i].j;
			ll x3 = s1.e[i].edgelabel;
			SN1.push_back(make_pair(x1,x2));
			edgelabel1.push_back(x3);
			if (N1.find(x1) == N1.end())
			{
				N1[x1] = j; //N2 code all vertex in large graph together order by appearance, this is a new vertex
				j ++;
			}
			if (N1.find(x2) == N1.end())
			{
				N1[x2] = j;
				j ++;
			}			
		}

		j = 1;
		for(short i = 0; i< s2.e.size(); i++){
			ll x1 = s2.e[i].i;
			ll x2 = s2.e[i].j;
			ll x3 = s2.e[i].edgelabel;
			SN2.push_back(make_pair(x1,x2));
			edgelabel2.push_back(x3);
			if (N2.find(x1) == N2.end())
			{
				N2[x1] = j; //N2 code all vertex in large graph together order by appearance, this is a new vertex
				j ++;
			}
			if (N2.find(x2) == N2.end())
			{
				N2[x2] = j;
				j ++;
			}			
		}
		
		j = 1;
		for(short i = 0; i< g.e.size(); i++){
			ll x1 = g.e[i].i;
			ll x2 = g.e[i].j;
			ll x3 = g.e[i].edgelabel;
			edgelabel2.push_back(x3);
			if (N3.find(x1) == N3.end())
			{
				N3[x1] = j; //N2 code all vertex in large graph together order by appearance, this is a new vertex
				j ++;
			}
			if (N3.find(x2) == N3.end())
			{
				N3[x2] = j;
				j ++;
			}			
		}

		//Find new_assumptions among shared vertex between s1 and s2
		vector<Lit> new_assumptions;
			
		//Find all shared vertex
		for(auto n2: N2){
			unordered_map<ll,ll>::const_iterator got = N1.find(n2.first);		
			if(got != N1.end()){//identify vertex of n2 in N1
				
				int curr_vertex = N1[n2.first]-1; // literal index in s1's SAT
				int curr_vertex_n2 = N2[n2.first]-1;// literal index in s2's SAT
				
				for(int i=0; i<N3.size();i++){
					if(last_result[curr_graph_index][N3.size()*curr_vertex+i] == 0) {
						new_assumptions.push_back(Lit(N3.size()*curr_vertex_n2+i,true));
					}
					if(last_result[curr_graph_index][N3.size()*curr_vertex+i] == 1) {
						new_assumptions.push_back(Lit(N3.size()*curr_vertex_n2+i,false));
					}
				}
				
			}
				
		}
		return new_assumptions; // vertex index is from 0
}

/*
 * SAT subgraph monomorphism function with neighbor MFS mapping assistant. 
 */
short SATSI(Graph & s, Graph & g)
{
		clock_t ss1 = clock();


		std::unordered_map<ll,ll> N1; // Subgraph
		std::unordered_map<ll,ll> N2; // Graph

		std::vector<std::pair<ll,ll> > SN1;
		std::vector<std::pair<ll,ll> > SN2;
		vector<ll> edgelabel1;
		vector<ll> edgelabel2;
		
		int j = 1;
		for(short i = 0; i< g.e.size(); i++){
			ll x1 = g.e[i].i;
			ll x2 = g.e[i].j;
			ll x3 = g.e[i].edgelabel;
			SN2.push_back(make_pair(x1,x2));
			edgelabel2.push_back(x3);
			if (N2.find(x1) == N2.end())
			{
				N2[x1] = j; //N2 code all vertex in large graph together order by appearance, this is a new vertex
				j ++;
			}
			if (N2.find(x2) == N2.end())
			{
				N2[x2] = j;
				j ++;
			}			
		}

		j = 1;

		for(short i = 0; i< s.e.size(); i++){
			ll x1 = s.e[i].i;
			ll x2 = s.e[i].j;
			ll x3 = s.e[i].edgelabel;
			SN1.push_back(make_pair(x1,x2));
			edgelabel1.push_back(x3);
			if (N1.find(x1) == N1.end())
			{
				N1[x1] = j; //N2 code all vertex in large graph together order by appearance, this is a new vertex
				j ++;
			}
			if (N1.find(x2) == N1.end())
			{
				N1[x2] = j;
				j ++;
			}			
		}

		ll n2 = N2.size();
		ll n1 = N1.size();
		
		std::vector<ll> adjg1 (n1);
		std::vector<ll> adjg2 (n2);
		std::vector<std::vector<ll>> edgeg1 (n1, std::vector<ll> (n1, 0));
		std::vector<std::vector<ll>> edgeg2 (n2, std::vector<ll> (n2, 0));

		for (int i = 0 ; i < SN2.size() ; i ++)			// all edges in large graph
		{
			ll x = N2[SN2[i].second];
			ll y = N2[SN2[i].first];
			adjg2[x-1]++;
			adjg2[y-1]++;
			edgeg2[x-1][y-1] = edgelabel2[i];//add edgelabel	
			edgeg2[y-1][x-1] = edgelabel2[i];//add edgelabel
		}

		for (int i = 0 ; i < SN1.size() ; i ++) //all edges in subgraph 
		{
			ll x = N1[SN1[i].first];
			ll y = N1[SN1[i].second];
			adjg1[x-1]++;
			adjg1[y-1]++;
			edgeg1[x-1][y-1] = edgelabel1[i];//add edgelabel
			edgeg1[y-1][x-1] = edgelabel1[i];//add edgelabel						
		}

		
		//Cryptominisat
		std::vector<ll> deg1 (n1);
		std::vector<ll> deg2 (n2);
		for(int i=0; i<n1; i++){
			deg1[i] = 0;
			for(int j=0; j<n1; j++){
				if(edgeg1[i][j] !=0)
					deg1[i]++;
			}
		}
		for(int i=0; i<n2; i++){
			deg2[i] = 0;
			for(int j=0; j<n2; j++){
				if(edgeg2[i][j] !=0)
					deg2[i]++;
			}
		}


		//Cryptominisat inilization 
		CMSat::SATSolver solver;
		solver.set_allow_otf_gauss();
		solver.set_polarity_auto();
		//solver.set_default_polarity(true);
		solver.set_no_equivalent_lit_replacement();
		solver.set_yes_comphandler();
		solver.set_up_for_scalmc();
		//solver->set_no_simplify();
		solver.set_no_bva();
		solver.set_no_bve();
		//solver.set_single_run();
		vector<CMSat::Lit> clause;
		
		solver.new_vars(n1*n2);
		

		for(int i=0; i<n1; i++){
			for(int j=0; j<n2; j++){
				if(deg1[i] > deg2[j]){
					clause.push_back(Lit(getvarno(n2,i,j), false));
					solver.add_clause(clause);
					clause.clear();					
				}		
			}		
		}
	
			
		for(int i=0 ; i<n1 ; i++){			//each pair of mapping vertex possible , use one varible to represent		
			for(int j = 0 ; j < n2 ; j ++){
					if(deg1[i] <= deg2[j])
						clause.push_back(Lit(getvarno(n2,i,j), true));
			}
			solver.add_clause(clause);
			clause.clear();
		}
		
		for(int i=0 ; i<n1; i++){
			for(int j = 0 ; j < n2 ; j ++){
				for(int k = j+1 ; k < n2 ; k ++){	
					if(deg1[i] <= deg2[j] && deg1[i] <= deg2[k]){ //if di > dj already false
						clause.push_back(Lit(getvarno(n2,i,j),false));
						clause.push_back(Lit(getvarno(n2,i,k),false));
						solver.add_clause(clause);
						clause.clear();	
					}
				}
			}
		}

		for(int i=0; i<n2; i++){
			for(int j=0; j<n1; j++){
				for(int k=j+1; k<n1; k++){
					if(deg1[j] <= deg2[i] && deg1[k] <= deg2[i]){
						clause.push_back(Lit(getvarno(n2,j,i),false));
						clause.push_back(Lit(getvarno(n2,k,i),false));
						solver.add_clause(clause);
						clause.clear();	
					}
				}
			}
		}

		for(int i=0 ; i<n1 ; i++){
			for(int j=0 ; j<n1 ; j++){
				if(edgeg1[i][j]!=0){
					for(int k=0 ; k<n2 ; k++){
						for (int l=0 ; l<n2 ; l++){
							if (edgeg2[k][l]==0){
									//degree
									if(deg1[i] <= deg2[k] && deg1[j] <= deg2[l]){
										clause.push_back(Lit(getvarno(n2,i,k),false));
										clause.push_back(Lit(getvarno(n2,j,l),false));
										solver.add_clause(clause);
										clause.clear();	
									}
								
							}
						}
					}
				}
			}
		}


		clock_t ee1 = clock();
		double time2 = (double)(ee1 - ss1)/CLOCKS_PER_SEC;
		cout<<" "<<time2;



		clock_t ss3 = clock();



		lbool ret2;
		unsigned int decision2;
		lbool ret;
		
		//get literal assignment from last_result for assumption, if there is last subgraph
		if(has_last_subgraph[curr_graph_index] == true){
			vector<Lit> new_assumptions = identify_same_vertex(last_subgraph[curr_graph_index], s, g);				
			ret2 = solver.solve(& new_assumptions);
			decision2 = solver.get_last_propagations();
			if(ret2 != l_True) {
			
				ret2 = solver.solve();
				decision2 += solver.get_last_propagations();
				
			}
			else if(ret2 == l_True){
				;//outputsinglegraph(s); 
			}
			ret = ret2;
		}
		
		if(has_last_subgraph[curr_graph_index] == false){
			
			ret = solver.solve();
		
			decision = solver.get_last_propagations();
		}
		if(ret == l_True){
			vector<lbool> result = solver.get_model();
		}
		decision = solver.get_last_propagations();

		//update last_subgraph, last_result, 
		//last_subgraph initilized as G vector, need to update 
		//vector<vector<int>> last_result;		  //assumptions assignment from last SAT test in G[0] G[1] G[2]
		//vector<Graphmy> last_subgraph;		  //last subgraph list queried by each graph     G[0] G[1] G[2]
		//vector<bool> has_last_subgraph;		  //bool to make sure has last subgraph query, with SATSI == 1
		//int curr_graph_index = -1;			  //curr graph of SATSI		
		if(curr_graph_index != -1 && ret == l_True){
			//update last_result
			vector<lbool> result = solver.get_model();
			last_result[curr_graph_index].clear();//clear last for update
						
			for(int i=0; i<result.size(); i++){
				if(result[i] == l_True)  last_result[curr_graph_index].push_back(1);
				if(result[i] == l_False) last_result[curr_graph_index].push_back(0);
			}
			
			//update last_subgraph
			last_subgraph[curr_graph_index] = s;
			//update has_last_subgraph
			has_last_subgraph[curr_graph_index] = true;		
		}
		
		if(curr_graph_index != -1 && ret == l_False){
			last_result[curr_graph_index].clear();
			has_last_subgraph[curr_graph_index] = false;
		}
		
		curr_graph_index = -1;
		
		
		clock_t ee3 = clock();
		double time3 = (double)(ee3 - ss3)/CLOCKS_PER_SEC;
		cout<<" "<<time3;

		
		if (ret == l_True) return 1;
		else return 0;	

}
/******************************************************************************************************
main
******************************************************************************************************/
int main(int argc, char* argv[]){
	
	// initialization
	filename = argv[1];
	initialization();
	
	//initial clock
	global_start = clock();
        clock_t start = clock();
	//initial random seed
        
        loadGraphs();
        
	//Initial MFS and its infrequent child subgraph as a Cut
	Cut initial;				
        		
	//Identify initial cut by remove edges from G_min: G[minindex]	
	if(cut_read_in_flag == 0){
		Graph re = findrepresentative();
       		if(re.e.size() == G[minindex].e.size()){
                	cout<<"Graph: "<<minindex<<" is biggest subgraph"<<endl;
                	return 0;
        	}
        	initial.setcut(re, representpath[representpath.size()-1]);
	}
	//get first cut by file
	if(cut_read_in_flag == 1){
		initial = loadrepresentative();	//first cut from file
	}
        
        //random walk in Margin space by initial the Cut (c, p)
        expandcut(initial);

        clock_t ends = clock();
}





