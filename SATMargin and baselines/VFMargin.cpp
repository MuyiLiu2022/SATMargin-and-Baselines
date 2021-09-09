/*Graphmy subpattern
compile:    g++ margin_cut_by_fileorcomputing.cpp -std=c++0x -o a
//g++ -std=c++11 VF2Margin.cpp -lcryptominisat5 -L/home/liu413/Desktop/cryptominisat/VF2/vf2lib-master/lib/ -I/home/liu413/Desktop/cryptominisat/VF2/vf2lib-master/include/ -lvf -lstdc++ -lm -o VF2Margin


//run: ./a 5_4.0.3.data 0.8 0.5 tmp.data 0 10 
*/
#include<time.h>				//add timer and genenrate random number
#include<limits>				//test data type limit 
#include<fstream>				//file read write
#include<iostream>				//std output
#include<iomanip>
#include<string>		
#include<sstream>
#include<cstdlib>
#include<typeinfo>
#include<stack>
#include<list>
#include<unordered_map>
#include<vector>
#include<sys/resource.h>			//memory usage
#include<stdlib.h>				//generate random number
#include<math.h>				//calculate exp
#include <sys/time.h>				//high resolution timer
//SAT head
#include <unordered_set>
#include <algorithm>
//VF head

#include "argraph.h"
#include "argedit.h"
#include "vf_mono_state.h"
#include <iostream>
#include <match.h>
#include <iostream>
#include <fstream>
#include <sys/time.h>				//high resolution timer
#include <argraph.h>
#include <argloader.h>
#include <allocpool.h>

/*
#include "minisat/utils/System.h"
#include "minisat/utils/ParseUtils.h"
#include "minisat/utils/Options.h"
#include "minisat/core/Dimacs.h"
#include "minisat/core/Solver.h"
#include "minisat/simp/SimpSolver.h"
*/
#include "cryptominisat5/cryptominisat.h"
#include <cassert>
using namespace CMSat;
using namespace std;

//VF2lib struct
// 
// Define class Point, with its I/O operators
//
class Point
  { public:
      float x, y;
  };

istream& operator>>(istream& in, Point &p)
  { in >> p.x >> p.y;
    return in;
  }

ostream& operator<<(ostream& out, Point &p)
  { out << p.x << ' ' << p.y;
    return out;
  }

// 
// Define class Empty, with its I/O operators
//
class Empty
  {
  };

istream& operator>>(istream& in, Empty &)
  { // Do nothing!
    return in;
  }

ostream& operator<<(ostream& out, Empty &)
  { // Do nothing!
    return out;
  }
bool my_visitor(int n, node_id ni1[], node_id ni2[], void *usr_data)
  { FILE *f = (FILE *)usr_data;

    // Prints the matched pairs on the file
        int i;
        for(i=0; i<n; i++)
          fprintf(f, "(%hd, %hd) ", ni1[i], ni2[i]);
        fprintf(f, "\n");

        // Return false to search for the next matching
        return false;
  }


//


//<class edge
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
//>end class edge
//<class graph
class Graphmy{
public:
	//short graphlength;
	vector<Edge> e;						//edge vector of graph
	vector<vector<short>> map;				//adjacent map
	vector<bool> vl;					//vertex list: True in graph False not in graph
	void setedges(short, short, short, short);		//set edges by class function
	void copy(Graphmy& g, Edge& last);			//initial by one more edge and graph
};
//set edge with edgeindex = index
void Graphmy::setedges(short index, short i, short j, short edgelabel){
	e[index].index = index;
	e[index].i = i;
	e[index].j = j;
	e[index].edgelabel = edgelabel;
}
void Graphmy::copy(Graphmy& g, Edge& last){
	for(short i=0; i<g.e.size(); i++){
		e.push_back(g.e[i]);		
	}
	e.push_back(last);
}
//> end class graph
//<class cut
class Cut{
public:
	vector<short> cl;					//graph child edge list
	vector<short> pl;					//graph parent edge list
	//string output;						//output for debug temporary
	void setcut(Graphmy &, short);				//set cut child and removed edge list
	void set(vector<short>& cl1, vector<short>& pl1);	//set by child and parent edgelist
};
void Cut::set(vector<short>& cl1, vector<short>& pl1){
	cl = cl1;
	pl = pl1;
}
//p: parent graph edgelist, edgeindex: last removed edge
void Cut::setcut(Graphmy& p, short edgeindex){
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
vector<Graphmy> G;				//graph dataset
short nedgelabel =4;				//number of edgelabel in this edgelabel system
vector<short> representpath;			//representative path from G[min] to a representative
short minindex;					//index of smallest graph in G[]
unordered_map<string, bool> hashmap;		//hashkey of explored cuts
double lowerenergy = 0.5;			//metropolis criterial
double equalenergy = 0.9;			//metropolis criterial

long int step =0;				//count steps used
clock_t global_start;				//global clock
clock_t global_end;
long int current_largest_sub = 0;		//current largest length subgraph found
string filename = "";				//graph.data.set filename
string cutfilename = "";			//current cut filename for second round search

double iso_usage = 0;				//isomophism time usage
unsigned int iso_num = 0;			//number of isomophism used

unsigned int nextcutratio = 10;			// the ratio of next cut type

unsigned int count_edge_mapping = 0;            //count number of edge mapping for performance
unsigned int decision = 0;                      //number of literal assignment

//functions declaration
/******************************************************************************************************
initialization and readin graphs
******************************************************************************************************/
void initialization();
void loadGraphmys();
/******************************************************************************************************
output functions for debug
******************************************************************************************************/
void outputmemoryusage();
void outputsinglegraph(Graphmy &);
void outputsingleedge(Edge &);
void outputmap(Graphmy &);
void outputvl(Graphmy &);
void outputgraph(Graphmy &);
void outputrepath();
void outputvector(vector<short>&);
void outputvector(vector<bool>&);
void outputcut(Cut&);
void outputstackusage(stack<Cut> cutstack);
/******************************************************************************************************
Memory usage functions
******************************************************************************************************/
static string memory_usage();
/******************************************************************************************************
Subgraph search: find representative
******************************************************************************************************/
short removeedge(Graphmy &g);			//remove one edge from g
short connectivity(Graphmy&);			//if connected graph
short findlargestvertex(Graphmy&); 		//find largest vertex in graph
void  adjacent(Graphmy &);			//update adjacent map in Graphmy 
short support(Graphmy& sub);			//find support of sub in G[], return support
bool  notused(short j, vector<short>);		//check if vertex used in stmp
short nextvertex(vector<short>, Graphmy);	//find next candidate for isomorphism to add one vertex in stmp
vector<short> mapnextvertex(short, vector<short>, vector<short>, Graphmy, Graphmy );
						//find a next vertex in Graphmy g which map to vertex nexts in Graphmy s
short isomorphism(Graphmy sub, Graphmy g);		//find sub isomorphism of sub in graph g
short smallestgraph();				//find smallest graph
Graphmy findrepresentative();			//find representative 
Cut loadrepresentative();			//NEW load representative from file after first round 
void savecutfile(Cut &cut);			//NEW save cut to cutfile for next round 
/******************************************************************************************************
Subgraph search: amble search surface
******************************************************************************************************/
short 		support(vector<short>& el);
short 		connectivity(vector<short>& el);
Graphmy 		el2graph(vector<short> el);
bool		vectorequal(vector<short>& v1, vector<short>& v2);
void 		onelessedge(vector<vector<short>>& re, vector<short>& cl, vector<short>& pl);
short 		elcomparation(vector<short>& el1, vector<short>& el2);
void		onemoreedge(vector<vector<short>>& call, vector<short>& pi, vector<short>& cl);
vector<short> 	commonparent(vector<short>& cl1, vector<short>& cl2);
void 		firstonelessedge(vector<short>& re, vector<short>& cl);
void		set_hash_key(vector<short>& curr);
bool		get_hash_key(vector<short>& curr);
void 		clear_hash_key();
void 		expandcut(Cut&);		//recursively expand all cuts on surface
//end functions declare
/******************************************************************************************************
Monte Carlo Random
******************************************************************************************************/
void random_onelessedge(vector<short>& cl, vector<short>& pl);	//used by get_type_pall()
void random_onemoreedge(vector<short>& ci, vector<short>& pi);	//used by get_type_call()

Cut get_type_pall(Cut& curr);
Cut get_type_call(Cut& curr);
Cut get_type_m(Cut& curr);
Cut get_type_s1(Cut& curr);

Cut get_next_cut(Cut& curr);			//get next cut to explore by random
short metropolis(short enew, short eold);	//metropolis criterial
short metropolis_1(short enew, short eold);	//metropolis by assigned probability
/******************************************************************************************************
SAT SI
******************************************************************************************************/
short 	SATSI(Graphmy& s, Graphmy& g);
short 	VFSI(Graphmy& s, Graphmy& g);
/******************************************************************************************************
initialization and readin graphs
******************************************************************************************************/
// initialization
void initialization(){
	/*cout<<"Please input How many edgelabel's in this edge label system:"<<endl;
	cin>>nedgelabel;
	cout<<"Please input the minimum support: "<<endl;
	cin>>minsupport;
	*/
}
//end initializationbool notused(short j, vector<short>&stmp)
//<store Graphmy data set
void loadGraphmys(){
	string line;
	ifstream graphdata(filename);

	Graphmy gg;
	gg.e.clear();
	Edge ee;

	short j = 0;
	short gl = -1;  					//graph length index
	short gn = 0; 						//graphs number index
	short index, ver1, ver2 , edg; 				//tmp for setting edge values
	while(graphdata >> line){	
		if(line.compare("@") == 0){			//edge separator
			j = 0;
			gl++;
		}
		if(line.compare("#") == 0){			//graph separator
			//gg.graphlength = gl + 1;
			G.push_back(gg);
			gg.e.clear();
			gl = -1;
			gn++;
		}
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
	//update adjacent map
	for(short i =0; i<G.size(); i++){
		adjacent(G[i]);
	}
}
//>end store Graphmy data set
/******************************************************************************************************
output functions for debug
******************************************************************************************************/
//facility output single graph
void outputsinglegraph(Graphmy &g){
	//cout<<"  length = "<<g.e.size()<<endl;
	for(short i = 0; i< g.e.size(); i++){
		cout<<"("<<g.e[i].i<<","<<g.e[i].j<<")";
	}cout<<endl;
}
//end facility outputsingle graph
//facility output memory usage
void outputmemoryusage(){
	cout<<"Current memory usage is : "<<memory_usage()<<endl;
}
//end output memory usage
//facility output single edge
void outputsingleedge(Edge & e){
	cout<<"Edge:"<<e.index<<" "<<e.i<<" "<<e.j<<" "<<e.edgelabel<<endl;
}
//end facility output single edge
//facility output adjacent map
void outputmap(Graphmy &g){
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
//end facility outputmap
//facility output vertex list
void outputvl(Graphmy &g){
	for(short i=0; i<g.vl.size(); i++){
		cout<<g.vl[i]<<" ";
	}cout<<endl;
}
//end facility output vertex list
//facility output graph with map and vl
void outputgraph(Graphmy &g){
	cout<<"<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<"<<endl;
	//cout<<"graph:"<<endl;
	//outputsinglegraph(g);
	//cout<<"map:"<<endl;
	//outputmap(g);
	//cout<<"vertex list:"<<endl;
	//outputvl(g);
	cout<<">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>"<<endl;
}
//end facility outputgraph
//facility output represent path
void outputrepath(){
	cout<<"Path to representative:"<<endl;	
	for(short i=0; i<representpath.size(); i++){
		cout<<representpath[i]<<" ";
	}cout<<endl;
}
//end facility outputrepath
//facility output a vector
void outputvector(vector<short>& ve){
	for(short i=0; i<ve.size(); i++){
		cout<<setw(4)<<ve[i];
	}cout<<endl;
}
//end outputvector
//facility output a vector
void outputvectorvector(vector<bool>& ve){
	for(short i=0; i<ve.size(); i++){
		cout<<setw(4)<<ve[i];
	}cout<<endl;
}
//end outputvector
//facility output cut
void outputcut(Cut& c){
	cout<<"<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<"<<endl;
	cout<<"Child: ";
	outputvector(c.cl);
	cout<<"Parent:";
	outputvector(c.pl);
	cout<<">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>"<<endl;
}
//end outputcut
//facility outputstackusage
void outputstackusage(stack<Cut> cutstack){
	cout<<"Stack size: "<<cutstack.size()<<endl;
}
//end outputstackusage
//facility outputmovetype
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
}
//end outputmovetype
/******************************************************************************************************
Memory usage functions
******************************************************************************************************/
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
//<remove one edge from Graphmy g, return the removed edge's edgeindex in G[min]
short removeedge(Graphmy &g){
	short graphlength = g.e.size();
	srand((unsigned)time(0)); 				//random seed
	short connect = 0;
	Graphmy tmp = g;						//backup graph g for restore
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
//>end remove one edge from graph g
//<test if a connected graph return 1 when connected 0 when not connected -1 when NULL graph
short connectivity(Graphmy& g){
	if(g.map.size() == 0)return -1;
	vector<bool> connection;
	for(short i=0; i<g.map.size(); i++){//initial
		connection.push_back(false);
	}
	stack<short> vstack;//vertex index 
	//use vl to choose entry point	
	short entrypoint;
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
	//for(short i=0; i<connection.size(); i++){cout<<connection[i]<<" ";}cout<<endl;
	//use vl to compair!!!	
	for(short i=0; i<connection.size(); i++){
		if(connection[i] == false && g.vl[i] == true){
			return 0;			
		}
	}
	return 1;
}
//>end connectivity
//<find largest vertex in graph
short findlargestvertex(Graphmy & g){
	short tmp = 0;
	for(short i = 0; i < g.e.size(); i++){
		if(g.e[i].i > tmp){tmp = g.e[i].i;}
		if(g.e[i].j > tmp){tmp = g.e[i].j;}
	}
	return tmp;
}
//>end find largest vertex in graph
//<update adjacent map in Graphmy g 
void adjacent(Graphmy &g){			//update adjacent map in Graphmy
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
		g.map[g.e[i].i][g.e[i].j] = g.e[i].edgelabel;		//g.e[i].index
		g.map[g.e[i].j][g.e[i].i] = g.e[i].edgelabel;		//g.e[i].index
		if(g.vl[g.e[i].i] == false){g.vl[g.e[i].i] = true;}
		if(g.vl[g.e[i].j] == false){g.vl[g.e[i].j] = true;}
	}
	return;
}
//>end adjacent
//<find support of subgraph sub in graphset G[], return support
short support(Graphmy& sub){
	short sup = 0;
	for(short i=0; i<G.size(); i++){
		if(i != minindex){//G[min] does not need to search
			//BFS
			clock_t ss = clock();
			//short iso = isomorphism(sub, G[i]);
			//sup = sup + iso;
			//cout<<"iso"<<iso<<endl;
			clock_t ee = clock();
			double time1 = (double)(ee - ss)/CLOCKS_PER_SEC;
			//cout<<time1<<" "<<count_edge_mapping*2<<" ";
			count_edge_mapping = 0;
			
			//SAT
			//clock_t ss1 = clock();
			//cout<<"G"<<i<<" ";
			//short	satiso = SATSI(sub, G[i]);
			//sup += satiso;
			
			//cout<<"sat"<<satiso<<endl;			
			//clock_t ee1 = clock();
			//double time2 = (double)(ee1 - ss1)/CLOCKS_PER_SEC;
			//cout<<sub.e.size()<<" "<<time2<<" "<<decision;
			
			
			
			//VF
			clock_t ss3 = clock();
			short vfre = VFSI(sub, G[i]);
			sup += vfre;
			//if(vfre != satiso) cout<<"!!"<<endl;
			
			clock_t ee3 = clock();
			double time3 = (double)(ee3 - ss3)/CLOCKS_PER_SEC;
			cout<<" "<<time3<<" "<<sub.e.size()<<endl;
			//if(vfre!=satiso) cout<<"!!!!!!!!!!!!!!!"<<endl;			
			decision = 0;
			

			
		}
	}
	sup++;//G[min] just plus 1
	return sup;
}
//>end support
//<vertex j not used in stmp return: true if not used, false if used
bool notused(short j, vector<short> stmp){
	for(short i=0; i<stmp.size(); i++){
		if(j == stmp[i]){
			return false;
		}
	}
	return true;
}
//>end not used
//<find candidate next vertex to extend stmp, used in isomorphism return is the vertex number or -1 when not possible
//!!!!maybe most linked candidate vertex is a better choice, which can rule out most impossbile links in gtmp
short nextvertex(vector<short>stmp, Graphmy s){
	//for(short i=0; i<stmp.size(); i++){cout<<stmp[i]<<" ";}cout<<endl;
	//outputmap(s);	
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
//>end nextvertex
//<map one next vertex in g to nexts which connected with vertices in gtmp, return -1 if no vertex possbile in g 
vector<short> mapnextvertex(short nexts, vector<short> stmp,vector<short> gtmp,Graphmy s, Graphmy g){
        vector<short> cand;
        //update used (gtmp) verteices in g     
        vector<bool> used;
        for(short i=0; i<g.map.size(); i++){
                used.push_back(false);
        }
        for(short i=0; i<gtmp.size(); i++){
                used[gtmp[i]] = true;   
        }
        //outputvector(used);
        //outputvector(gtmp);
        //
        
        for(short i=0; i<g.map.size(); i++){//all vertex in g
                if(used[i] == false){//not used in gtmp
                        short flag = 1;
                        for(short j=0; j<stmp.size(); j++){//all used vertex in stmp
                                if(s.map[nexts][stmp[j]] != -1){//stmp[j] connected with nexts
                                        
					count_edge_mapping++;//count number of edge mapping for statitic

					//vertex j connect with vertices in gtmp which are connected in stmp in same label
                                        /*undirected                                    
                                        //consider direction of edge i (edgelabel == 1)
                                        if(s.map[nexts][stmp[j]] == 1){
                                                if(nexts-stmp[j]>0 && i-gtmp[j]<0){
                                                        flag = -1;
                                                        break;
                                                }
                                                if(nexts-stmp[j]<0 && i-gtmp[j]>0){
                                                        flag = -1;
                                                        break;
                                                }
                                        }
                                        //end consider direction of edge i (edgelabel == 1)
                                        */                                      
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
//>end mapnextvertex
//<find isomorphism subgraph sub in graph g, return 1 when at least one, 0 when none
short isomorphism(Graphmy s, Graphmy g){
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
	//outputgraph(s);
	//outputgraph(g);
	vector<short> sone;				//vertex map in sub
	vector<short> gone;				//vertex map in g	
	short i=0; 
	while(s.vl[i] == false){
		i++;	
	}
	sone.push_back(i);				//add first vertex in subone
	for(short i=g.vl.size()-1; i>=0; i--){		//add possible vertex in g as map of first vertex in subone
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
		//vector<vector<short>> childpi(vector<short>& pi)for(short i=0; i<stmp.size(); i++){cout<<stmp[i]<<" ";}cout<<endl;
		//for(short i=0; i<gtmp.size(); i++){cout<<gtmp[i]<<" ";}cout<<endl;		
		sstack.pop();
		gstack.pop();
		lstack.pop();
		
		//cout<<"vlength: "<<vlength<<" svlength: "<<svlength<<endl;
		//!!!! need termination condition 		
		if(vlength == svlength){
			//outputmap(s);cout<<endl;
			//outputmap(g);cout<<endl;
			
			/*cout<<"@@@@@"<<endl;		
			cout<<"subgraph:"<<endl;
			outputvector(stmp);
			cout<<"graph:"<<endl;			
			outputvector(gtmp);
			cout<<"#####"<<endl;
			*/
			iso_e = clock();				    		//add timer end
			iso_usage = iso_usage + (double)(iso_e-iso_s)/CLOCKS_PER_SEC;	//add time usage to total		
			return 1;
		}
		short nexts = nextvertex(stmp, s);//get next candidate vertex add to stmp
		vector<short> nextg = mapnextvertex(nexts, stmp, gtmp, s, g);//try to find all vertex in g which map to nexts
		//cout<<nextg.size()<<endl;
		//prepare stmp, gtmp and vlength then push into stack
		stmp.push_back(nexts);//put candidate in vertex list of stmp		
		vlength++;//prepare for push into lstack		
		for(short i = nextg.size()-1; i>= 0; i--){		
						
			gtmp.push_back(nextg[i]);//put candidate in vertex list of gtmp
						
			sstack.push(stmp);
			gstack.push(gtmp);
			lstack.push(vlength);
			
			gtmp.pop_back();
		}
		
	}
	iso_e = clock();				    		//add timer end
	iso_usage = iso_usage + (double)(iso_e-iso_s)/CLOCKS_PER_SEC;	//add time usage to total
	return 0;
}
//
//find smallest graph in graph dataset, return index of smallest graph in global short min
short smallestgraph(){
	short minsize = G[0].e.size();		//inital number of edge in smallest graph			
	short index = 0;			//intial smallest graph index
	for(short i = 1; i<G.size(); i++){
		if(minsize > G[i].e.size()){
			index = i;
			minsize = G[i].e.size();
		}
	}
	return index;
}
//end smallestgraph
//<find representative subgraph which is f(cut) node in lattice
Graphmy findrepresentative(){
	minindex = smallestgraph();
	Graphmy re = G[minindex];
	while(support(re) < G.size()){
		//cout<<re.e.size()<<endl;
		representpath.push_back(removeedge(re));
	}
	return re;
}
//>end findrepresentative

//< NEW load current cut from file
Cut loadrepresentative(){
	ifstream cutdata(cutfilename);
	Cut currcut;		//curr cut to right in
   	short cpflag = 0;	//child parent flag 1: read in child 2: read in parent
	string letter;
	short currnum = 0;	//current number
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
//>end load current cut from file
//<output current cut to file
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
//>end output cut to file

/******************************************************************************************************
Subgraph search: amble surface
******************************************************************************************************/
//<count support by edgelist of a subgraph
short support(vector<short>& el){
	if(connectivity(el) == 0 || el.size()<= 1){		// must be connectted
		return 0;
	}
	Graphmy curr = el2graph(el);//edgelist2graph
	return support(curr);
}
//>end support
//<connectivity by edgelist
short connectivity(vector<short>& el){
	Graphmy curr = el2graph(el);
	return connectivity(curr);
}
//>end connectivity
//<convert edgelist to graph
Graphmy el2graph(vector<short> el){
	Graphmy g;
	for(short i=0; i<el.size(); i++){
		g.e.push_back(G[minindex].e[el[i]]);
	}
	adjacent(g);
	return g;
}
//>end el2graph
//<vector equal, return true when equal false when not equal
bool vectorequal(vector<short>& v1, vector<short>& v2){
	for(short i=0; i<v1.size(); i++){
		if(v1[i] != v2[i]){return false;}
	}
	return true;
}
//>
//<remove one edge from cl, return all connected one less edge graph candidate edgelist which is not equal to pl
void onelessedge(vector<vector<short>>& re, vector<short>& cl, vector<short>& pl){
	vector<short> curr;	
	re.clear();	
	//choose ith edge	
	for(short i=0; i<cl.size(); i++){
		curr = cl;
		curr.erase(curr.begin() + i);
		if(connectivity(curr) == 1){
			//if(!vectorequal(pl, curr)){		//curr must be not equal to pl which is parent of initial cut
				re.push_back(curr);
			//}
		}
	}
}
//>end oneless edge
//<first graph of function onelessedge
void firstonelessedge(vector<short>& re, vector<short>& cl){
	for(short i=0; i<cl.size(); i++){
		re = cl;
		re.erase(re.begin() + i);
		//outputvector(cl);
		//outputvector(re);
		//if(connectivity(re) == 1){		//connected
		if(support(re) == G.size()){		//frequent
			//cout<<"support s1 pld= "<<support(re)<<endl;
			return;	
		}
		//}
	}
	re.clear();
	//cout<<"fault"<<endl;
}
//>end fistonelessedge
//<edgelist comparation return 1 when equal, 0 when not equal
short elcomparation(vector<short>& el1, vector<short>& el2){
	for(short i=0; i<el1.size(); i++){
		if(el1[i] != el2[i]){
			return 0;
		}
	}
	return 1;
}
//>end elcomparation
//<get candidates of one more edge children edgelist of pi except cl, first parameter is edgelist vector for return
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
			if(connectivity(curr) == 1){		//need to think about
				//if(!vectorequal(cl, curr)){				
					call.push_back(curr);	//return edgelist of currg
				//}			
			}
		}
	}
}
//>end childpi
//<find common parent of two nodes, return edgelist of common parent
vector<short> commonparent(vector<short>& cl1, vector<short>& cl2){
	vector<short> re;				//common parent
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
	//outputvector(re);
	return re;
}
//>end commonparent
//<set hash key: put explored cut into hash table
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
//>end set hash key
//<get hash key: find if cut already in hash table return 1 when has this key, 0 when no this key
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
//>end get hash key 
//<clear hash key: clear all cuts in hash table, only for monte carlo random
void clear_hash_key(){
	hashmap.clear();
}
//>end clear hash key
//<recursive function to explore all cuts, cut& initial: initial cut
void expandcut(Cut& initial){
	stack<Cut> cutstack;
	cutstack.push(initial);
	//high resolution timer	
	timeval t1, t2;
	double elapsedTime;
        
	while(!cutstack.empty() ){
		//global_start = clock();		//count global clock to stop
		gettimeofday(&t1, NULL);
		
		step++;	
		//cout<<step<<" "<<cutstack.top().pl.size()<<endl;	
		Cut curr = cutstack.top();
		cutstack.pop();
		//set_hash_key(curr);							//count how many different cuts explored
		//cout<<hashmap.size()<<endl;
		//outputcut(curr);		
		//cout<<"curr size = "<<curr.pl.size()<<endl;
		//cout<<step<<endl;
		if(current_largest_sub < curr.pl.size()){
			current_largest_sub = curr.pl.size();					//current largest fre subgraph length	
		}	
		
		cutstack.push(get_next_cut(curr));					//set next step's cut//choose next cut type by random
		//accept 1 or reject 0 a new cut step or return a NULL cut		
		while(cutstack.top().cl.size() == 0 
		|| cutstack.top().pl.size() == 0
		|| metropolis_1(cutstack.top().pl.size(),curr.pl.size()) == 0){			
				
								
				cutstack.pop();				
				cutstack.push(get_next_cut(curr));
							
		}
		//global_end = clock();
		gettimeofday(&t2, NULL);
		
		elapsedTime = (t2.tv_sec - t1.tv_sec) * 1000.0;
		elapsedTime += (t2.tv_usec - t1.tv_usec) / 1000.0;   		
		//cout << elapsedTime << " ms\n";

		//cout<<global_end<<" "<<global_start<<endl;
		//cout<<(global_end - global_start)<<endl;
		//cout<<(double)CLOCKS_PER_SEC<<endl;
	}
}
//>end expandcut
/******************************************************************************************************
Monte Carlo Random
******************************************************************************************************/
//<random one less edge: remove one edge in cl to build pl, return is in pl
void random_onelessedge(vector<short>& cl, vector<short>& pl){
	short index = rand()%(cl.size());
	//cout<<index<<" ";	
	pl = cl;	
	pl.erase(pl.begin() + index);
}
//>end random one less edge
//<random one more edge: add one edge in pi  to build ci, return in ci
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
}
//>end random one more edge
//<get type 0(pall) next cut
Cut get_type_pall(Cut& curr){
	Cut re;
	re.cl = curr.cl;
	random_onelessedge(re.cl, re.pl);
	short count = 0;
	while(support(re.pl) < G.size() && count <= G[minindex].e.size()){		//support test includes connectivity test
		//outputmovetype(0);
		count++;								//break while loop
		
		re.cl = curr.cl;		
		random_onelessedge(re.cl, re.pl); 
		
	}
	if(count > G[minindex].e.size()){Cut null;null.pl.clear();null.cl.clear();return null;}		//did not find new cut
	return re;
}
//>end get type 0 next cut
//<get type 1(call) next cut
Cut get_type_call(Cut& curr){
	Cut re;
	Cut pall = get_type_pall(curr);
	if(pall.pl.size() == 0){Cut null;null.pl.clear();null.cl.clear();return null;}	//did not find any pall
	re.pl = pall.pl;
	random_onemoreedge(re.cl, re.pl);
	short count = 0;
	while(support(re.cl) == G.size() && count <= G[minindex].e.size()){		
			
		//outputmovetype(1);
		count++;

		pall = get_type_pall(curr);
		re.pl = pall.pl;
		random_onemoreedge(re.cl, re.pl);
	}
	if(count > G[minindex].e.size()){Cut null;null.pl.clear();null.cl.clear();return null;}		//did not find new cut
	return re;
}
//>end end get type 1 next cut
//<get type 2 next cut
Cut get_type_m(Cut & curr){
	Cut re;
	Cut pall = get_type_pall(curr);
	if(pall.pl.size() == 0){Cut null;null.pl.clear();null.cl.clear();return null;}			//did not find any pall	
	re.pl = pall.pl;
	random_onemoreedge(re.cl, re.pl);
	short count = 0;
	while(support(re.cl) < G.size() && count <= G[minindex].e.size()){		
		//outputmovetype(2);		
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
//>end get type 2 next cut
//<get type 3 next cut s1
Cut get_type_s1(Cut & curr){
	Cut re;
	re.cl = curr.cl;
	random_onelessedge(re.cl, re.pl);
	short count = 0;
	while(support(re.pl) == G.size() && count <= G[minindex].e.size()){		//support test includes connectivity test	
		//outputmovetype(3);
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
//>end get type 3 next cut s1
//< add edge to pi subgraph to form frequent subgraph
void random_replaceedge(vector<short>& ci, vector<short>& pi){ 
        vector<short> ptmp = pi;
        int i = 6;
        while(i>0){
                i--;
                short edgeindex = rand()%(G[minindex].e.size());
                while(!notused(G[minindex].e[edgeindex].index, ptmp)){
                        //cout<<"iteration"<<i<<endl;
                        //outputvector(ptmp);
                        //cout<<"support"<<support(ptmp)<<endl;
                        edgeindex = rand()%(G[minindex].e.size());
                }
                short index = G[minindex].e[edgeindex].index;
                short shift = 0;
                while(ptmp[shift]<index && shift< ptmp.size()){
                        //cout<<"loop2";
                        shift++;
                }
                ptmp.insert(ptmp.begin()+shift, index);
                if(support(ptmp) == G.size()){
                        //cout<< "re.pl support"<<support(ptmp)<<endl;
                        //cout<< "re.pl size"<<ptmp.size()<<endl;
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
//<get global type
Cut get_type_global(Cut & curr){
	Cut re;

	re.pl = curr.pl;
	re.cl = curr.cl;		
	
	//cout<<"om"<<endl;
	random_replaceedge(re.cl, re.pl);
	//cout<<"dsf"<<endl;
	
	return re;
}
//>end get type 3 next cut s1

//<get next cut
Cut get_next_cut(Cut& curr){
	short cut_type = rand()%nextcutratio;	//4 types of cut: pall, call, m and s1
	Cut re;				//next cut
	//cut_type = 5;	//debug	
	if(cut_type >= 4){//debug
		re = get_type_global(curr);	
	}	

	if(cut_type == 0){
		//cout<<"pall"<<endl;		
		re = get_type_pall(curr);
		//cout<<"call"<<endl;
	}
	if(cut_type == 1){
		re = get_type_call(curr);
	}
	if(cut_type == 2){
		//cout<<"m"<<endl;		
		re = get_type_m(curr);
	}
	if(cut_type == 3){
		//cout<<"s1"<<endl;
		re = get_type_s1(curr);
	}

	return re;
}
//>end get next cut
//<metropolis criterion to accept newly generated cut 
//parameter: generated random number vs exp(deltaE/KT) (first version for try), short temperature is T here
//return: 0 not accept new cut, 1 accept new cut
short metropolis(short enew, short eold){
	//cout<<enew<<" "<<eold<<endl;
	//cout<<"metropolist: "<<endl;
	double K = 1.0;
	double temperature = 1.0;
	double r_num = 1.0;					//random number in [0, 1]	
	
	//generate random number
	//srand((unsigned)time(0));				//get seeds at the beginning of program
	r_num = (double)rand()/(RAND_MAX);
	//cout<<"random num =     "<<r_num<<endl;

	//exp(delta(E)/KT)	
	double m_value = 0.0;					//metropolis criterion value to compare with random number
	m_value = exp((enew-eold)/(K*temperature));
	//cout<<"metropolis num = "<<m_value<<endl;
	
	if(r_num <= m_value){
		cout<<"accept"<<endl;		
		return 1;
	}
	else{
		cout<<"not accept"<<endl;
		return 0;	
	}
	
}
//>end metropolis
//<metropolis_1: metropolis by assigned probability
//return: 0 not accept new cut, 1 accept new cut
short metropolis_1(short enew, short eold){
	if(enew > eold){
		//cout<<endl;
		//cout<<"accept_!"<<endl;
		return 1;
	}
	if(enew == eold){
		double r_num = 0.0;
		r_num = (double)rand()/(RAND_MAX);
		//cout<<"enew == eold, rnum"<<r_num<<endl;
		if(r_num <= equalenergy){
			//cout<<endl;			
			//cout<<"accept_!"<<endl;
			return 1;
		}
		else{
			//cout<<endl;
			//cout<<"not accept_!"<<endl;			
			return 0;		
		}
	}
	if(enew < eold){
		double r_num = 0.0;
		r_num = (double)rand()/(RAND_MAX);
		//cout<<"enew < eold, rnum"<<r_num<<endl;		
		if(r_num <= lowerenergy){
			//cout<<endl;			
			//cout<<"accept_!"<<endl;
			return 1;
		}

		else{
			//cout<<endl;			
			//cout<<"not accept_!"<<endl;
			return 0;		
		}
	}
	return 0;
}
//>end metropolis_1
/******************************************************************************************************
SAT SI
******************************************************************************************************/
typedef long long ll;

ll getvarno(ll n2, ll j, ll i)
{
	return (n2*j + i + 1)-1;
}

struct pairhash {
public:
  template <typename T, typename U>
  std::size_t operator()(const std::pair<T, U> &x) const
  {
    return std::hash<T>()(x.first) ^ std::hash<U>()(x.second);
  }
};

void outputmap(unordered_map<ll,ll> &curr){
	cout<<"graph"<<endl;
	for(auto c:curr){
		cout<<c.first<<" "<<c.second<<endl;
	}
	cout<<endl;
	return;
}
void outputboolmatrix(std::vector<std::vector<bool>> & G1){
	for(auto GG : G1){
		for(auto G : GG){
			cout<<G<<" ";
		}cout<<endl;
	}
	cout<<endl;
	return;
}
void outputlongmatrix(std::vector<std::vector<ll>> & G1){
	for(auto GG : G1){
		for(auto G : GG){
			cout<<G<<" ";
		}cout<<endl;
	}
	cout<<endl;
	return;
}
short SATSI(Graphmy& s, Graphmy& g)
{
		//cout<<"SATSI"<<endl;
		std::unordered_map<ll,ll> N1; // small graph
		std::unordered_map<ll,ll> N2; // large graph

		std::vector<std::pair<ll,ll> > SN1;
		std::vector<std::pair<ll,ll> > SN2;
		//self add edgelabel of edges
		vector<ll> edgelabel1;
		vector<ll> edgelabel2;
		//end
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
		//cout<<n2<<" "<<n1<<endl;

		//std::vector<std::vector<bool> > EdgesG1 (n1, std::vector<bool> (n1, false));
		//std::vector<std::vector<bool> > EdgesG2 (n2, std::vector<bool> (n2, false));

		//std::vector<ll> AdjG2_out (n2);
		//std::vector<ll> AdjG1_out (n1);
		//std::vector<ll> AdjG2_in (n2);
		//std::vector<ll> AdjG1_in (n1);
		
		//self	
		std::vector<ll> adjg1 (n1);
		std::vector<ll> adjg2 (n2);
		std::vector<std::vector<ll>> edgeg1 (n1, std::vector<ll> (n1, 0));
		std::vector<std::vector<ll>> edgeg2 (n2, std::vector<ll> (n2, 0));
		//end

		for (int i = 0 ; i < SN2.size() ; i ++)// all edges in large graph
		{
			ll x = N2[SN2[i].second];
			ll y = N2[SN2[i].first];
			//AdjG2_in[ x - 1] ++; // in degree of vertex
			//AdjG2_out[ y - 1] ++;// out degree of vertex
			//EdgesG2[y-1][x-1] = true; //adjacency matrix Note: y is first x is second!!!!
			//self
			adjg2[x-1]++;
			adjg2[y-1]++;
			edgeg2[x-1][y-1] = edgelabel2[i];//add edgelabel	
			edgeg2[y-1][x-1] = edgelabel2[i];//add edgelabel
			//end
					
		}

		for (int i = 0 ; i < SN1.size() ; i ++) //all edges in subgraph 
		{
			ll x = N1[SN1[i].first];
			ll y = N1[SN1[i].second];
			//AdjG1_out[x - 1] ++; // this is out different from G2 big
			//AdjG1_in[y - 1] ++;
			//EdgesG1[x-1][y-1]= true;
			//self
			adjg1[x-1]++;
			adjg1[y-1]++;
			edgeg1[x-1][y-1] = edgelabel1[i];//add edgelabel
			edgeg1[y-1][x-1] = edgelabel1[i];//add edgelabel			
			//end
			
		}

		//outputlongmatrix(edgeg1);
		//outputlongmatrix(edgeg2);
		
		//cryo
		
		CMSat::SATSolver solver;
		vector<CMSat::Lit> clause;
		
		//output mapping from vertex i vertex j to var self
		for (int i = 0 ; i < n1 ; i ++)//each impossible pair of vertex in small > big graphs
		{
			for (int j = 0 ; j < n2 ; j ++)
			{
				//cout<< i<<" "<< j << " "<<getvarno(n2,i,j)<<endl;
				solver.new_var();
			}
		}
		
		//
		// file ready.
		//FILE * fp;
		//fp = fopen("/home/xinling/Desktop/xorsample/SI/MMC-Marign_SAT_labels_undirected/new.graphs.satinput","w");
		// ffout.open();
		//fprintf(fp, "p cnf %lld %lld\n", n1*n2, (n1 + n1*(n2*(n2-1))/2 + n2*(n1*(n1-1))/2 + n1*(n1-1)*n2*(n2-1)/4));


		std::unordered_set<pair<ll,ll>, pairhash > NotPoss;
		
		//self undirect
		std::unordered_set<pair<ll,ll>,pairhash> notpossundirect;
		//end

		for (int i = 0 ; i < n1 ; i ++)//each impossible pair of vertex in small > big graphs
		{
			for (int j = 0 ; j < n2 ; j ++)
			{
				//if (AdjG2_out[j] < AdjG1_out[i] || AdjG2_in[j] < AdjG1_in[i]) //impossible pair Not possible since subgraph vertex degree larger
				//	NotPoss.insert(std::make_pair(i,j));
				//self
				if (adjg2[j] < adjg1[i]){//impossible pair Not possible since subgraph vertex degree larger
					notpossundirect.insert(std::make_pair(i,j));
					//cout<<"not possible"<<endl;				
				}				
				//end
			}
		}

		for (int i = 0 ; i < n1 ; i ++)//each pair of mapping vertex possible , use one varible to represent
		{

			string s = ""; //cannot be 1 at the same time
			//Minisat::vec<Minisat::Lit> currclause;//literals
			for (int j = 0 ; j < n2 ; j ++)
			{
				std::pair<ll,ll> p = std::make_pair(i,j);
				//if (notpossundirect.find(p) == notpossundirect.end())
					s += to_string(getvarno(n2,i,j)) + " ";
					
					//cout<<literals.size()<<" "<<getvarno(n2,i,j)<<endl;
					clause.push_back(Lit(getvarno(n2,i,j), true));
					//currclause.push(literals[getvarno(n2,i,j)]);// each var
					
			}
			s += "0\n";
			//solver.addClause(currclause);
			solver.add_clause(clause);
			clause.clear();
			//fprintf(fp, "%s", s.c_str());
		}
		
		for (int i = 0 ; i < n1 ; i ++)// ij or ik and ....
		{
			for (int j = 0 ; j < n2 ; j ++)
			{
				for (int k = j+1 ; k < n2 ; k ++)
				{
					//Minisat::vec<Minisat::Lit> literals;// each literals
					pair<ll,ll> p1 = std::make_pair(i,j);
					pair<ll,ll> p2 = std::make_pair(i,k);
					
					//if (notpossundirect.find(p1) == notpossundirect.end() && notpossundirect.find(p2) == notpossundirect.end()){
						//fprintf(fp, "-%lld -%lld 0\n", getvarno(n2,i,j), getvarno(n2,i,k));
						//solver.addClause(~literals[getvarno(n2,i,j)],~literals[getvarno(n2,i,k)]);
						clause.push_back(Lit(getvarno(n2,i,j),false));
						clause.push_back(Lit(getvarno(n2,i,k),false));
						solver.add_clause(clause);
						clause.clear();	
			
						//literals.push(~Minisat::mkLit(getvarno(n2,i,j)));
						//literals.push(~Minisat::mkLit(getvarno(n2,i,k)));
						//solver.addClause(literals);
					//}

				}
			}
		}

		for (int i = 0 ; i < n2 ; i ++)// ji or ki and ...
		{
			for (int j = 0 ; j < n1 ; j ++)
			{
				for (int k = j+1 ; k < n1  ; k ++)
				{
					pair<ll,ll> p1 = std::make_pair(j,i);
					pair<ll,ll> p2 = std::make_pair(k,i);
					//if (notpossundirect.find(p1) == notpossundirect.end() && notpossundirect.find(p2) == notpossundirect.end()){
						//fprintf(fp, "-%lld -%lld 0\n", getvarno(n2,j,i), getvarno(n2,k,i));
						//solver.addClause(~literals[getvarno(n2,j,i)],~literals[getvarno(n2,k,i)]);
						clause.push_back(Lit(getvarno(n2,j,i),false));
						clause.push_back(Lit(getvarno(n2,k,i),false));
						solver.add_clause(clause);
						clause.clear();	
			
					//}
				}
			}
		}

		for (int i = 0 ; i < n1 ; i ++)
		{
			for (int j = 0 ; j < n1 ; j ++)
			{
				if (i != j)
				{
					for (int k = 0 ; k < n2 ; k ++)
					{
						for (int l = 0 ; l < n2 ; l ++)
						{
							if (k != l)
							{
								pair<ll,ll> ik = std::make_pair(i,k);
								pair<ll,ll> jl = std::make_pair(j,l);
								if (edgeg1[i][j]!=0 && edgeg2[k][l]==0 || 
								    edgeg1[i][j]!=0 && edgeg1[i][j]!=edgeg2[k][l] 
								 
								//&& NotPoss.find(ik) == NotPoss.end() 
								//&& NotPoss.find(jl) == NotPoss.end()
								){
									//fprintf(fp, "-%lld -%lld 0\n", getvarno(n2,i,k), getvarno(n2,j,l));
									//solver.addClause(~literals[getvarno(n2,i,k)],~literals[getvarno(n2,j,l)]);
									clause.push_back(Lit(getvarno(n2,i,k),false));
									clause.push_back(Lit(getvarno(n2,j,l),false));
									solver.add_clause(clause);
									clause.clear();	
			
									//cout<<"-"<<getvarno(n2,i,k)<<"-"<<getvarno(n2,j,l)<<" "<<i<<j<<k<<l<<endl;
									//cout<<edgeg1[i][j]<<edgeg2[][j]<<endl;
								}
							}
						}
					}
				}
			}
		}


		//clock_t ss1 = clock();
		lbool ret = solver.solve();		
		//print_clause_stats();
		//cout<<"lastconflicts"<<solver.get_last_conflicts()<<endl;
		/*
		if(ret == l_True){
			outputsinglegraph(s);
			outputsinglegraph(g);

			vector<lbool> result = solver.get_model();
			for(int i=0; i<result.size(); i++){
				if(result[i] == l_True) cout<<"1";
				if(result[i] == l_False) cout<<"0";
			}cout<<endl;
			
		}*/
		//solver.print_stats();
		decision = solver.get_last_propagations();
		//clock_t ee1 = clock();
		//double time2 = (double)(ee1 - ss1)/CLOCKS_PER_SEC;
		//cout<<"solve"<<"\t"<<time2<<"\t";
		if (ret == l_True) return 1;
		else return 0;	
}


short VFSI(Graphmy& s, Graphmy& g)
{
		
		clock_t ss1 = clock();
		
		
		//cout<<"SATSI"<<endl;
		std::unordered_map<ll,ll> N1; // small graph
		std::unordered_map<ll,ll> N2; // large graph

		std::vector<std::pair<ll,ll> > SN1;
		std::vector<std::pair<ll,ll> > SN2;
		//self add edgelabel of edges
		vector<ll> edgelabel1;
		vector<ll> edgelabel2;
		//end
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
		//cout<<n2<<" "<<n1<<endl;

		//std::vector<std::vector<bool> > EdgesG1 (n1, std::vector<bool> (n1, false));
		//std::vector<std::vector<bool> > EdgesG2 (n2, std::vector<bool> (n2, false));

		//std::vector<ll> AdjG2_out (n2);
		//std::vector<ll> AdjG1_out (n1);
		//std::vector<ll> AdjG2_in (n2);
		//std::vector<ll> AdjG1_in (n1);
		
		//self	
		std::vector<ll> adjg1 (n1);
		std::vector<ll> adjg2 (n2);
		std::vector<std::vector<ll>> edgeg1 (n1, std::vector<ll> (n1, 0));
		std::vector<std::vector<ll>> edgeg2 (n2, std::vector<ll> (n2, 0));
		//end

		for (int i = 0 ; i < SN2.size() ; i ++)// all edges in large graph
		{
			ll x = N2[SN2[i].second];
			ll y = N2[SN2[i].first];
			//AdjG2_in[ x - 1] ++; // in degree of vertex
			//AdjG2_out[ y - 1] ++;// out degree of vertex
			//EdgesG2[y-1][x-1] = true; //adjacency matrix Note: y is first x is second!!!!
			//self
			adjg2[x-1]++;
			adjg2[y-1]++;
			edgeg2[x-1][y-1] = edgelabel2[i];//add edgelabel	
			edgeg2[y-1][x-1] = edgelabel2[i];//add edgelabel
			//end
					
		}

		for (int i = 0 ; i < SN1.size() ; i ++) //all edges in subgraph 
		{
			ll x = N1[SN1[i].first];
			ll y = N1[SN1[i].second];
			//AdjG1_out[x - 1] ++; // this is out different from G2 big
			//AdjG1_in[y - 1] ++;
			//EdgesG1[x-1][y-1]= true;
			//self
			adjg1[x-1]++;
			adjg1[y-1]++;
			edgeg1[x-1][y-1] = edgelabel1[i];//add edgelabel
			edgeg1[y-1][x-1] = edgelabel1[i];//add edgelabel			
			//end
			
		}

		//VF2 format
		/*
		cout<<"Subgraph#############################################################"<<endl;
		cout<<"#number of node"<<endl;
		cout<<n1<<endl;
		cout<<"#node list"<<endl;
		for( int i = 0; i<n1; i++){
			cout<<i<<" 1"<<endl;
		}
		
		for( int i = 0; i<n1; i++){
			int sum = 0;
			for(int k=i+1; k<n1; k++){
				if (edgeg1[i][k]!=0)sum++;
			}
			cout<<"#number of edge of i"<<endl;
			cout<<sum<<endl;
			cout<<"#edgelist"<<endl;
			for(int j=i+1;j<n1;j++){
				if (edgeg1[i][j]!=0){
					cout<<i<<" "<<j<<" "<<"1"<<endl;
				}
			}
		}
		cout<<"endsubgraph#############################################################"<<endl;
		
		//
		cout<<"Graph#############################################################"<<endl;
		cout<<"#number of node"<<endl;
		cout<<n2<<endl;
		cout<<"#node list"<<endl;
		for( int i = 0; i<n2; i++){
			cout<<i<<" 1"<<endl;
		}
		
		for( int i = 0; i<n2; i++){
			int sum = 0;
			for(int j=0;j<n2;j++){
				if (edgeg2[i][j]!=0 && i != j){
					sum++;
				}
			}
			cout<<"#number of edge of i"<<endl;
			cout<<sum<<endl;
			cout<<"#edgelist"<<endl;
			for(int j=0;j<n2;j++){
				if (edgeg2[i][j]!=0 && i != j){
					cout<<i<<" "<<j<<" "<<"1"<<endl;
				}
			}
		}
		cout<<"endgraph#############################################################"<<endl;
		*/
		
		//generate subgraph 
		ARGEdit subgraph;  // The object used to create the graph
	        // Insert the four nodes
        	for(int i=0; i<n1; i++)
          		subgraph.InsertNode(NULL); // The inserted node will have index i.
                  
                for( int i = 0; i<n1; i++){
			for(int j=i+1;j<n1;j++){
				if (edgeg1[i][j]!=0){
					subgraph.InsertEdge(i, j, NULL); // NULL stands for no sem. attribute.
				}
			}
		}
               //end generate subgraph
     		
     		
     		//generate graph
     		ARGEdit graph;  // The object used to create the graph
	        
	        for( int i = 0; i<n2; i++){
			graph.InsertNode(NULL); // The inserted node will have index i.
		}
		
		for( int i = 0; i<n2; i++){
			for(int j=0;j<n2;j++){
				if (edgeg2[i][j]!=0 && i != j){
					graph.InsertEdge(i, j, NULL);
				}
			}
		}
		
     		// Now the Graph can be constructed...
        	Graph ggg(&graph);
        	Graph sss(&subgraph);
	
		clock_t ee1 = clock();
		double time2 = (double)(ee1 - ss1)/CLOCKS_PER_SEC;
		cout<<" "<<time2;
		
		
		VFMonoState  s0(&sss, &ggg);
 		int n;
		node_id ni1[1000], ni2[1000];
	
		clock_t ss3 = clock();
		bool re = match(&s0, &n, ni1, ni2);
		clock_t ee3 = clock();
		double time3 = (double)(ee3 - ss3)/CLOCKS_PER_SEC;
		cout<<" "<<time3;
		
		if(re == 1) return 1;
		else {return 0;}
}

/******************************************************************************************************
main
******************************************************************************************************/
int main(int argc, char* argv[]){
	
	filename = argv[1];

	istringstream ss2(argv[2]);
	ss2>>equalenergy;
	
	istringstream ss1(argv[3]);
	ss1>>lowerenergy;

	cutfilename = argv[4];
	//cout<<argc<<endl;
	
	//method option of initial cut read in     0: generate by computation 1:read in from data
	short cut_read_in_flag = 0;
	istringstream ss3(argv[5]);
	ss3>>cut_read_in_flag;
	//cout<<cut_read_in_flag<<endl;	
	
	nextcutratio = 10;
	istringstream ssn(argv[6]);
	ssn>>nextcutratio;
	
	
	//initial clock
	global_start = clock();
        clear_hash_key();
	step = 0;
        clock_t start = clock();
	//initial random seed
        srand((unsigned)time(0));
	srand(rand());
        initialization();
        
        loadGraphmys();
        

	Cut initial;				//first cut
        		
	//get first cut by caculation	
	if(cut_read_in_flag == 0){
		Graphmy re = findrepresentative();
       		if(re.e.size() == G[minindex].e.size()){
                	cout<<"Graphmy: "<<minindex<<" is biggest subgraph"<<endl;
                	return 0;
        	}
        	
        	initial.setcut(re, representpath[representpath.size()-1]);
	}
	//get first cut by file
	if(cut_read_in_flag == 1){
		initial = loadrepresentative();	//first cut from file
	}
        
        expandcut(initial);

        clock_t ends = clock();
	
        //cout<<(double)(ends - start)/(CLOCKS_PER_SEC)<<"\t"
    	//    <<step<<"\t"
	//    <<hashmap.size()<<"\t"
	//    <<current_largest_sub<<"\t"
	//    <<iso_num<<"\t"
	//    <<iso_usage
	//    <<endl;
	
}





