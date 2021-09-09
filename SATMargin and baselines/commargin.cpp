/*Graph subpattern
*/
#include<time.h>				//add timer
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
using namespace std;

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
class Graph{
public:
	//short graphlength;
	vector<Edge> e;						//edge vector of graph
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
//> end class graph
//<class cut
class Cut{
public:
	vector<short> cl;					//graph child edge list
	vector<short> pl;					//graph parent edge list
	//string output;						//output for debug temporary
	void setcut(Graph &, short);				//set cut child and removed edge list
	void set(vector<short>& cl1, vector<short>& pl1);	//set by child and parent edgelist
};
void Cut::set(vector<short>& cl1, vector<short>& pl1){
	cl = cl1;
	pl = pl1;
}
//p: parent graph edgelist, edgeindex: last removed edge
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
short minindex;					//index of smallest graph in G[]
unordered_map<string, bool> hashmap;		//hashkey of explored cuts

short currbiggest = 0;				//current biggest cut length (frequent parent subgraph length)
unsigned long long cutnum = 0;			//number of total cut explored
string filename = "";				//graph.data.set filename
clock_t sss;					//timer for each hour output starter
clock_t eee;					//timer for each hour output ender
stack<Cut> cutstack;				//cutstack in expandcut function
//functions declaration
/******************************************************************************************************
initialization and readin graphs
******************************************************************************************************/
void initialization();
void loadGraphs();
/******************************************************************************************************
output functions for debug
******************************************************************************************************/
void outputmemoryusage();
void outputsinglegraph(Graph &);
void outputsingleedge(Edge &);
void outputmap(Graph &);
void outputvl(Graph &);
void outputgraph(Graph &);
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
short removeedge(Graph &g);			//remove one edge from g
short connectivity(Graph&);			//if connected graph
short findlargestvertex(Graph&); 		//find largest vertex in graph
void  adjacent(Graph &);			//update adjacent map in Graph 
short support(Graph& sub);			//find support of sub in G[], return support
bool  notused(short j, vector<short>&);		//check if vertex used in stmp
short nextvertex(vector<short>&, Graph&);	//find next candidate for isomorphism to add one vertex in stmp
vector<short> mapnextvertex(short&, vector<short>&, vector<short>&, Graph&, Graph &);
						//find a next vertex in Graph g which map to vertex nexts in Graph s
short isomorphism(Graph& sub, Graph g);		//find sub isomorphism of sub in graph g
short smallestgraph();				//find smallest graph
Graph findrepresentative();			//find representative 
/******************************************************************************************************
Subgraph search: amble search surface
******************************************************************************************************/
short 		support(vector<short>& el);
short 		connectivity(vector<short>& el);
Graph 		el2graph(vector<short> el);
bool		vectorequal(vector<short>& v1, vector<short>& v2);
void 		onelessedge(vector<vector<short>>& re, vector<short>& cl, vector<short>& pl);
short 		elcomparation(vector<short>& el1, vector<short>& el2);
void		onemoreedge(vector<vector<short>>& call, vector<short>& pi, vector<short>& cl);
vector<short> 	commonparent(vector<short>& cl1, vector<short>& cl2);
void 		firstonelessedge(vector<short>& re, vector<short>& cl);
void		set_hash_key(vector<short>& curr);
bool		get_hash_key(vector<short>& curr);
void 		expandcut(Cut&);						//recursively expand all cuts on surface
//end functions declare

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
//<store Graph data set
void loadGraphs(){
	string line;
	ifstream graphdata(filename);

	Graph gg;
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
//>end store Graph data set
/******************************************************************************************************
output functions for debug
******************************************************************************************************/
//facility output single graph
void outputsinglegraph(Graph &g){
	cout<<"  length = "<<g.e.size()<<endl;
	for(short i = 0; i< g.e.size(); i++){
		cout<<"@"<<setw(4)<<g.e[i].index<<setw(4)<<g.e[i].i<<setw(4)<<g.e[i].j<<setw(4)<<g.e[i].edgelabel<<endl;
	}cout<<"#"<<endl;
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
//end facility outputmap
//facility output vertex list
void outputvl(Graph &g){
	for(short i=0; i<g.vl.size(); i++){
		cout<<g.vl[i]<<" ";
	}cout<<endl;
}
//end facility output vertex list
//facility output graph with map and vl
void outputgraph(Graph &g){
	cout<<"<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<"<<endl;
	cout<<"graph:"<<endl;
	outputsinglegraph(g);
	cout<<"map:"<<endl;
	outputmap(g);
	cout<<"vertex list:"<<endl;
	outputvl(g);
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
	cout<<"<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<"<<endl;
	cout<<"Child: ";
	outputvector(c.cl);
	cout<<"Parent:";
	outputvector(c.pl);
	cout<<">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>"<<endl;
}
//end outputcut
//facility outputstackusage
void outputstackusage(stack<Cut> cutstack){
	cout<<"Stack size: "<<cutstack.size()<<endl;
}
//end outputstackusage
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
//<remove one edge from Graph g, return the removed edge's edgeindex in G[min]
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
//>end remove one edge from graph g
//<test if a connected graph return 1 when connected 0 when not connected -1 when NULL graph
short connectivity(Graph& g){
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
short findlargestvertex(Graph & g){
	short tmp = 0;
	for(short i = 0; i < g.e.size(); i++){
		if(g.e[i].i > tmp){tmp = g.e[i].i;}
		if(g.e[i].j > tmp){tmp = g.e[i].j;}
	}
	return tmp;
}
//>end find largest vertex in graph
//<update adjacent map in Graph g 
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
		g.map[g.e[i].i][g.e[i].j] = g.e[i].edgelabel;		//g.e[i].index
		g.map[g.e[i].j][g.e[i].i] = g.e[i].edgelabel;		//g.e[i].index
		if(g.vl[g.e[i].i] == false){g.vl[g.e[i].i] = true;}
		if(g.vl[g.e[i].j] == false){g.vl[g.e[i].j] = true;}
	}
	return;
}
//>end adjacent
//<find support of subgraph sub in graphset G[], return support
short support(Graph& sub){
	short sup = 0;
	for(short i=0; i<G.size(); i++){
		if(i != minindex){//G[min] does not need to search						
			sup = sup + isomorphism(sub, G[i]);
		}
	}
	sup++;//G[min] just plus 1
	return sup;
}
//>end support
//<vertex j not used in stmp return: true if not used, false if used
bool notused(short j, vector<short>&stmp){
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
short nextvertex(vector<short>&stmp, Graph& s){
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
vector<short> mapnextvertex(short& nexts, vector<short>& stmp,vector<short>& gtmp,Graph &s, Graph &g){
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
					//vertex j connect with vertices in gtmp which are connected in stmp in same label
					//consider direction of edge i (edgelabel == 1)					
					/*if(s.map[nexts][stmp[j]] == 1){ 
						if(nexts-stmp[j]>0 && i-gtmp[j]<0){
							flag = -1;
							break;
						}
						if(nexts-stmp[j]<0 && i-gtmp[j]>0){
							flag = -1;
							break;
						}
					}*/
					//end consider direction of edge i (edgelabel == 1)					
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
short isomorphism(Graph& s, Graph g){
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
		//output each hour
                eee = clock();
                if((double)(eee - sss)/CLOCKS_PER_SEC>60){
                        //running time
                        cout<<setw(10)<<(double)(eee - sss)/CLOCKS_PER_SEC;
                        sss = clock();
                        //biggest cut length
                        cout<<setw(10)<<currbiggest;
                        //total number of cut
                        cout<<setw(10)<<cutnum;
                        //total cut in stack
                        cout<<setw(20)<<cutstack.size();
                        //memory usage
                        cout<<setw(26)<<memory_usage()<<endl;
                }
		//

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
		//!!!! need terminate condition 		
		if(vlength == svlength){
			//outputmap(s);cout<<endl;
			//outputmap(g);cout<<endl;
			//outputvector(stmp);			
			//outputvector(gtmp);
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
	
	return 0;
}
//
//find smallest graph, return index of smallest graph in global short min
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
Graph findrepresentative(){
	minindex = smallestgraph();
	Graph re = G[minindex];
	while(support(re) < G.size()){
		representpath.push_back(removeedge(re));
	}
	return re;
}
//>end findrepresentative
/******************************************************************************************************
Subgraph search: amble surface
******************************************************************************************************/
//<count support by edgelist of a subgraph
short support(vector<short>& el){
	Graph curr = el2graph(el);//edgelist2graph
	return support(curr);
}
//>end support
//<connectivity by edgelist
short connectivity(vector<short>& el){
	Graph curr = el2graph(el);
	return connectivity(curr);
}
//>end connectivity
//<convert edgelist to graph
Graph el2graph(vector<short> el){
	Graph g;
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
		if(connectivity(re) == 1){		//connected
			if(support(re) == G.size()){	//frequent
				return;	
			}
		}
	}
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
	vector<short> re;					//common parent
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
//<recursive function to explore all cuts, cut& initial: initial cut
void expandcut(Cut& initial){
	//stack<Cut> cutstack;
	cutstack.push(initial);
	set_hash_key(initial);
	sss = clock();
	while(!cutstack.empty()){	
		Cut curr = cutstack.top();
		//record if is the current biggest cut
		if(curr.pl.size() > currbiggest){
			currbiggest = curr.pl.size();
		}		
		//
		//number of cut explored
		cutnum++;
		//
				
		cutstack.pop();
		//outputcut(curr);
		//cout<<curr.output<<endl;
		//cout<<"hash size: "<<hashmap.size()<<"	";
		//outputstackusage(cutstack);
		vector<vector<short>> pall;						//one less edge graphs of cl
		onelessedge(pall, curr.cl, curr.pl);					//get vector of graph edgelists
		for(short i=0; i<pall.size(); i++){					//all one less edge graphs	
			if(support(pall[i]) == G.size()){				//frequent
				//outputvector(pall[i]);				//output result !!!!
				/*if(pall[i].size() >=18){
					cout<<"			";
					outputvector(pall[i]);		
				}*/
				vector<vector<short>> call;				//child edgelist vector of pall[i]
				onemoreedge(call, pall[i], curr.cl);			//get vector of graph edgelists		
				for(short j=0; j<call.size(); j++){
					//outputvector(call[j]);
					if(support(call[j]) < G.size()){		//infrequent
						Cut add;				//add to cutstack
						add.set(call[j], pall[i]);
						//add.output = "pall";
						if(!get_hash_key(add)){			//has not been explored
							set_hash_key(add);							
							cutstack.push(add);		//push to stack
						}
					}
					else{						//frequent
						Cut add;
						vector<short> m;								
						m = commonparent(call[j], curr.cl);	//find common parent M	
						add.set(m, call[j]);
						//add.output = "M";
						if(!get_hash_key(add)){
							set_hash_key(add);
							cutstack.push(add);
						}
					}				
				}
			}
			else{								//infrequent
				vector<short> s1;					//s1				
				firstonelessedge(s1, pall[i]);
				Cut add;
				add.set(pall[i], s1);
				//add.output = "si";
				if(!get_hash_key(add)){
					set_hash_key(add);
					cutstack.push(add);					//put s1 in stack
				}			
			}
		}	
	}
}
//>end expandcut
/******************************************************************************************************
main
******************************************************************************************************/
int main(int argc, char* argv[]){
	filename = argv[1];

	initialization();

	loadGraphs();
	//representative timer
	clock_t rstart = clock();
	Graph re = findrepresentative();
	if(re.e.size() == G[minindex].e.size()){
		cout<<"Graph: "<<minindex<<" is biggest subgraph"<<endl;
		return 0;
	}	
	clock_t rend = clock();
	//cout<<"representative time costed:"<<(double)(rend - rstart)/CLOCKS_PER_SEC;
	//
	Cut initial;
	initial.setcut(re, representpath[representpath.size()-1]);
	
	//timerstart	
	clock_t start = clock();
	expandcut(initial);
	clock_t ends = clock();
	
	//cout if can be finished
	cout<<"finishing"<<endl;	
	//running time	
	cout<<setw(10)<<(double)(ends - start)/CLOCKS_PER_SEC;
	//biggest cut length
	cout<<setw(10)<<currbiggest;
	//total number of cut	
	cout<<setw(10)<<cutnum;
	//memory usage 	
	cout<<setw(26)<<memory_usage()<<endl;		
}
