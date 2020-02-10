/** This code has been taken from readCnf of bfss and suitably modified - SS **/

#include <iostream>
#include <cstdio>
#include <fstream>
#include <cassert>
#include <string.h>
#include <vector>
#include <set>
#include <map>
#include <queue>
#include <algorithm>
#include <boost/range/adaptor/reversed.hpp>

using namespace std;

#define MAX_DEP_SIZE 5

//Currently for an unary universal variable - a wire definition is generated.
//This should be changed if it doesn't meet the specifications. - SS

vector<vector<int> > allClauses;
vector<bool> tseitinClauses;
vector<int> varsX;
vector<int> varsY;
vector<int> unates;
int numVars, numClauses;

vector<set<int> > existsAsPos;
vector<set<int> > existsAsNeg;
vector<map<int,int> > posImplies;
vector<map<int,int> > negImplies;

map<int, vector<int> > depAND;
map<int, vector<int> > depOR;
map<int, vector<int> > depXOR;
set<int> depCONST;
set<int> depTRUE;
set<int> depFALSE;
vector<bool> depFound;

queue<int> litToPropagate;

void readCnf0 (char * qdFileName);
void readQdimacsFile(char * qdFileName);
void print(vector<int> & v);
void print(set<int> & v);
void findDependencies();
bool findDepAND(int y);
bool findDepOR(int y);
bool findDepXOR(int y);
void findLitToProp();
void propagateLiteral(int lit);
void writeVerilogFile(string fname, string moduleName);
int addFlatClausesToVerilog(ofstream&ofs, int start, int end, int&nextVar);
void writeVariableFile(string fname);
void writeDependenceFile(string fname);
string vecToVerilogLine(vector<int> &v, string op);
void writeNonTseitinToQdimacsFile(string fname);
static inline void addToImpliesMap(map<int,int>&m, int lit, int clauseNum);
static inline void processBinaryClause(int clauseNum);
static inline void setConst(int lit);
static inline map<int,int>& getImpliesMap(int lit);
bool checkForCycles();
bool DFS_checkForCycles(vector<set<int> >& graph, int node, vector<int>& DFS_startTime, vector<int>& DFS_endTime, int& DFS_currTime);
void reduceDependencySizes();

inline string varNumToName(int v) {
	return ("v_"+to_string(v));
}
inline string extraNumToName(int v) {
	return ("x_"+to_string(v));
}

#ifdef MAIN
int main(int argc, char * argv[]) {
    char * qdFileName;
    if ( argc < 2 ) {
        cout << "Wrong number of command-line arguments. Usage: readCnf qdimacs_filename " << endl;
        return 1;
    }
    qdFileName = argv[1];

    readCnf0(qdFileName);
}
#endif
void readCnf0 ( char * qdFileName)
{
	string baseFileName(qdFileName);
	baseFileName = baseFileName.substr(baseFileName.find_last_of("/") + 1);  //Get the file name;
	baseFileName.erase(baseFileName.find (".qdimacs"), string::npos); //This contains the code for the raw file name;
	cout << "BaseName:     " << baseFileName << endl;

	string varFileName = baseFileName + "_var.txt";
	string aigFileName = baseFileName + ".v" ;
	string depFileName = baseFileName + "_dep.txt" ;
	string qdmFileName = baseFileName + ".qdimacs.noUnary" ;

	readQdimacsFile(qdFileName);
	cout << "Finished readQdimacsFile" << endl;

	// Propagate unary clauses (and more)
	findLitToProp();
	cout << "Finished findLitToProp" << endl;

	while(!litToPropagate.empty()) {
		int toProp = litToPropagate.front();
		litToPropagate.pop();
		propagateLiteral(toProp);
	}
	cout << "Finished propagateLiteral" << endl;

	writeNonTseitinToQdimacsFile(qdmFileName);

	findDependencies();
	cout << "Finished findDependencies" << endl;

	assert(!checkForCycles());
	cout << "Finished checkForCycles" << endl;

	reduceDependencySizes();
	cout << "Finished reduceDependencySizes" << endl;

	int numNonTseitin = 0;
	for(int i = 0; i < allClauses.size(); i++) {
		if(!tseitinClauses[i]) {
			numNonTseitin++;
			// cout<<i<<": \t"; print(allClauses[i]);
		}
	}
	cout << "depCONST.size(): " << depCONST.size() << endl;
	cout << "numNonTseitin:   " << numNonTseitin << endl;

	writeVerilogFile(aigFileName, baseFileName);
	writeVariableFile(varFileName);
	writeDependenceFile(depFileName);
}

void readQdimacsFile(char * qdFileName) {
    char C[100], c;
    int tmpVar;

	FILE *qdFPtr = fopen (qdFileName, "r");

	// Number of variables and clauses
	fscanf (qdFPtr, "%c", &c);
	fscanf (qdFPtr, "%s", C);
	while (strcmp (C, "cnf") != 0)
		fscanf (qdFPtr, "%s", C);
	fscanf(qdFPtr, "%d %d", &numVars, &numClauses); // read first line p cnf
	cout << "numVars:       " <<  numVars << endl;
	cout << "NumClauses:   " << numClauses << endl;

	// Vars X
	fscanf (qdFPtr, "%c", &c);
	while (c != 'a')
		fscanf (qdFPtr, "%c", &c);

	fscanf(qdFPtr, "%d", &tmpVar);
	while (tmpVar !=0) {
		varsX.push_back(tmpVar);
		fscanf(qdFPtr, "%d", &tmpVar);
	}
	cout << "varsX.size(): " << varsX.size() << endl;
	assert (numVars > varsX.size());

	// Vars Y (to elim)
	fscanf (qdFPtr, "%c", &c);

	while (c != 'e')
		fscanf (qdFPtr, "%c", &c);
	fscanf(qdFPtr, "%d", &tmpVar);
	while (tmpVar !=0) {
		varsY.push_back(tmpVar);
		fscanf(qdFPtr, "%d", &tmpVar);
	}
	cout << "varsY.size(): " << varsY.size() << endl;
	assert (numVars > varsY.size());

	// Update numVars = maxVar
	int maxVar = 0;
	for(auto it:varsX)
		maxVar = max(maxVar,it);
	for(auto it:varsY)
		maxVar = max(maxVar,it);
	cout << "maxVar:       " << maxVar << endl;
	if(maxVar < numVars) {
		cout << "Setting numVars = " << maxVar << endl;
		numVars = maxVar;
	}

	existsAsPos.resize(numVars+1);
	existsAsNeg.resize(numVars+1);
	posImplies.resize(numVars+1, map<int,int>());
	negImplies.resize(numVars+1, map<int,int>());
	depFound.resize(numVars+1, false);

	// Clauses
	for (int i = 0; i < numClauses ; i++) {
		vector<int> tempClause;
		fscanf(qdFPtr, "%d", &tmpVar);
		while (tmpVar != 0) {
			tempClause.push_back(tmpVar);
            if (tmpVar > maxVar)
                cerr << " Variable not defined " << tmpVar <<endl;
			else if(tmpVar > 0) { // pos
				existsAsPos[tmpVar].insert(i);
			}
			else { // neg
				existsAsNeg[-tmpVar].insert(i);
			}
			fscanf(qdFPtr, "%d", &tmpVar);
		}

		if(!tempClause.empty()) {
			allClauses.push_back(tempClause);
			tseitinClauses.push_back(false);
		}

		if(tempClause.size() == 2) { // populate ___Implies
			processBinaryClause(allClauses.size()-1);
		}
	}

	fclose (qdFPtr);
}

void findDependencies() {
	// Find AND dependencies
	for(auto y:boost::adaptors::reverse(varsY)) {
		depFound[y] = depFound[y] or findDepAND(y) or findDepOR(y);
	}
	for(auto y:boost::adaptors::reverse(varsY)) {
		depFound[y] = depFound[y] or findDepXOR(y);
	}
}

bool findDepAND(int y) {
	// Check for y = AND(...)
	for(auto clauseNum: existsAsPos[y]) { // Checking all possible clauses

		if(tseitinClauses[clauseNum] == true)
			continue;

		bool gotcha = true;
		for(auto v2: allClauses[clauseNum]) {
			//if(tseitinClauses[clauseNum] == true) //Required - SS?
			//	continue;
			if(v2!=y and posImplies[y].find(-v2)==posImplies[y].end()) {
				gotcha = false;
				break;
			}
		}
		if(gotcha) {
			// Print it
			string dep = "AND(";
			for(auto v2: allClauses[clauseNum]) {
			//	if(tseitinClauses[clauseNum] == true) //Required - SS?
		//			continue;
				if(v2!=y) {
					dep = dep + to_string(-v2) + ", ";
				}
			}
			dep = dep.substr(0,dep.length()-2) + ")";
			cout << "DEP" << y << " = " << dep << endl;

			// Found Dependency
			// assert(depAND.find(y) == depAND.end());
			depAND[y] = vector<int>();
			for(auto v2: allClauses[clauseNum]) {
				//if(tseitinClauses[clauseNum] == true)
				//	continue;
				if(v2!=y) {
					depAND[y].push_back(-v2);
					tseitinClauses[posImplies[y][-v2]] = true; // tseitinClauses=true
				}
			}
			tseitinClauses[clauseNum] = true; // tseitinClauses=true
			return true;
		}
	}
	return false;
}

bool findDepOR(int y) {
	// Check for -y = AND(...)
	for(auto clauseNum: existsAsNeg[y]) { // Checking all possible clauses

		if(tseitinClauses[clauseNum] == true)
			continue;

		bool gotcha = true;
		for(auto v2: allClauses[clauseNum]) {
			if(tseitinClauses[clauseNum] == true)
				continue;
			if(v2!=-y and negImplies[y].find(-v2)==negImplies[y].end()) {
				gotcha = false;
				break;
			}
		}
		if(gotcha) {
			// Print it
			string dep = "OR(";
			for(auto v2: allClauses[clauseNum]) {
				if(tseitinClauses[clauseNum] == true)
					continue;
				if(v2!=-y) {
					dep = dep + to_string(v2) + ", ";
				}
			}
			dep = dep.substr(0,dep.length()-2) + ")";
			cout << "DEP" << y << " = " << dep << endl;

			// Found Dependency
			// assert(depOR.find(y) == depOR.end());
			depOR[y] = vector<int>();
			for(auto v2: allClauses[clauseNum]) {
				if(tseitinClauses[clauseNum] == true)
					continue;
				if(v2!=-y) {
					depOR[y].push_back(v2);
					tseitinClauses[negImplies[y][-v2]] = true; // tseitinClauses=true
				}
			}
			tseitinClauses[clauseNum] = true; // tseitinClauses=true
			return true;
		}
	}
	return false;
}

bool findDepXOR(int y) {
	// Check for y = XOR(...)
	for(auto clauseNum: existsAsPos[y]) { // Checking all possible clauses

		auto & cl1 = allClauses[clauseNum];
		if(tseitinClauses[clauseNum] == true or cl1.size()!=3)
			continue;

		int iTemp = 0;
		vector<int> otherVars(2);
		if(cl1[iTemp]==y)
			iTemp++;
		otherVars[0] = cl1[iTemp];
		iTemp++;
		if(cl1[iTemp]==y)
			iTemp++;
		otherVars[1] = cl1[iTemp];
		iTemp++;

		for(auto clauseNum2: existsAsPos[y]) { // Checking all possible clauses

			auto & cl2 = allClauses[clauseNum2];
			if(tseitinClauses[clauseNum2] == true or cl2.size()!=3
				or clauseNum==clauseNum2)
				continue;

			if(find(cl2.begin(),cl2.end(),-otherVars[0])!=cl2.end()
				and find(cl2.begin(),cl2.end(),-otherVars[1])!=cl2.end()) {

				int clause1foundAt = -1;
				int clause2foundAt = -1;
				for(auto clauseNum3: existsAsNeg[y]) { // Checking all possible clauses
					auto & cl3 = allClauses[clauseNum3];
					if(tseitinClauses[clauseNum3] == true or cl3.size()!=3
						or clauseNum3==clauseNum2 or clauseNum3==clauseNum)
						continue;

					if(find(cl3.begin(),cl3.end(),otherVars[0])!=cl3.end()
						and find(cl3.begin(),cl3.end(),-otherVars[1])!=cl3.end()) {
						clause1foundAt = clauseNum3;
					}
					if(find(cl3.begin(),cl3.end(),-otherVars[0])!=cl3.end()
						and find(cl3.begin(),cl3.end(),otherVars[1])!=cl3.end()) {
						clause2foundAt = clauseNum3;
					}
				}
				if(clause1foundAt != -1 and clause2foundAt != -1) {
					// Print it
					string dep = "XOR(" + to_string(otherVars[0]) + ", " + to_string(-otherVars[1]) + ")";
					cout << "DEP" << y << " = " << dep << endl;

					// Found Dependency
					vector<int> res(2);
					res[0] = otherVars[0];
					res[1] = -otherVars[1];
					depXOR[y] = res;

					tseitinClauses[clauseNum] = true;	// tseitinClauses=true
					tseitinClauses[clauseNum2] = true;	// tseitinClauses=true
					tseitinClauses[clause1foundAt] = true;	// tseitinClauses=true
					tseitinClauses[clause2foundAt] = true;	// tseitinClauses=true

					return true;
				}
			}
		}
	}
	return false;
}

void print(vector<int> & v) {
	for(auto it:v)
		cout << it << " ";
	cout << endl;
}

void print(map<int, int> & v) {
	for(auto it:v)
		cout << "(" << it.first << "," << it.second << ") ";
	cout << endl;
}

void print(set<int> & v) {
	for(auto it:v)
		cout << it << " ";
	cout << endl;
}

void findLitToProp() {
	for(int clauseNum = 0; clauseNum < allClauses.size(); clauseNum++) {
		auto & clause = allClauses[clauseNum];
       // cout << "clause " << clauseNum << " has size " << clause.size () << endl;
		if(clause.size() == 1) {
        //    cout << "Setting " << clause[0] << " to const " << endl;
			setConst(clause[0]);
			if (std::find (varsX.begin(), varsX.end(), abs (clause [0])) != varsX.end())
				cout << " A universally quantified variable is unary " << clause[0] << endl;

			tseitinClauses[clauseNum] = true; // Unary tseitinClauses=true
		}
		else if(clause.size() == 2) {
			int v0 = clause[0];
			int v1 = clause[1];

			// -v1 -> v0, check if v1 -> v0, then v0_isConst
			// -v0 -> v1, check if v0 -> v1, then v1_isConst

			map<int,int>& v0_map = getImpliesMap(v0);
			map<int,int>& v1_map = getImpliesMap(v1);

			if(v1_map.find(v0) != v1_map.end()) { // v0_isConst
				setConst(v0);
				tseitinClauses[clauseNum] = true;	// Unary tseitinClauses=true
				tseitinClauses[v1_map[v0]] = true;	// Unary tseitinClauses=true
			}
			if(v0_map.find(v1) != v0_map.end()) { // v1_isConst
				setConst(v1);
				tseitinClauses[clauseNum] = true;	// Unary tseitinClauses=true
				tseitinClauses[v0_map[v1]] = true;	// Unary tseitinClauses=true
			}
		}
	}

	// findPureLiterals
	for (auto var : varsY) {
		if(existsAsPos[var].empty()) {
			// set var = 0
			cout << "PureNeg" << endl;
			setConst(-var);
		}
		else if(existsAsNeg[var].empty()) {
			// set var = 1
			cout << "PurePos" << endl;
			setConst(var);
		}
	}
}

void propagateLiteral(int lit) {
	int var = abs(lit);
	cout << " Propogating literal " << lit << endl;
	bool pos = lit>0;
	for(auto clauseNum:existsAsPos[var]) {
		if(tseitinClauses[clauseNum])
			continue;
		if(pos) {
			tseitinClauses[clauseNum] = true;	// tseitinClauses=true
		}
		else{
			// Remove var from allClauses
			auto it = find(allClauses[clauseNum].begin(), allClauses[clauseNum].end(), var);
			assert(it != allClauses[clauseNum].end());
			*it = allClauses[clauseNum].back();
			allClauses[clauseNum].resize(allClauses[clauseNum].size()-1);

			assert(!allClauses[clauseNum].empty()); // CNF formula is unsat
			if(allClauses[clauseNum].size() == 1) {
				setConst(allClauses[clauseNum][0]);
				tseitinClauses[clauseNum] = true;	// Unary tseitinClauses=true
			}
			else if(allClauses[clauseNum].size() == 2) {
				processBinaryClause(clauseNum);
			}
		}
	}

	for(auto clauseNum:existsAsNeg[var]) {
		if(tseitinClauses[clauseNum])
			continue;
		if(!pos) {
			tseitinClauses[clauseNum] = true;	// Unary tseitinClauses=true
		}
		else{
			// Remove var from allClauses
			auto it = find(allClauses[clauseNum].begin(), allClauses[clauseNum].end(), -var);
			assert(it != allClauses[clauseNum].end());
			*it = allClauses[clauseNum].back();
			allClauses[clauseNum].resize(allClauses[clauseNum].size()-1);

			assert(!allClauses[clauseNum].empty()); // CNF formula is unsat
			if(allClauses[clauseNum].size() == 1) {
				setConst(allClauses[clauseNum][0]);
				tseitinClauses[clauseNum] = true;	// Unary tseitinClauses=true
			}
			else if(allClauses[clauseNum].size() == 2) {
				processBinaryClause(clauseNum);
			}
		}
	}

	if(pos) {
		existsAsNeg[var].clear();
	}
	else{
		existsAsPos[var].clear();
	}
}

void writeVerilogFile(string fname, string moduleName) {
	ofstream ofs (fname, ofstream::out);
	ofs << VERILOG_HEADER;
	ofs << "module " << moduleName << " ";
	ofs << "(";
	for(auto it:varsX) {
		if(!depFound[it])
		ofs << varNumToName(it) << ", ";
	}
	for(auto it:varsY) {
		if(!depFound[it])
			ofs << varNumToName(it) << ", ";
	}
	ofs << "o_1);" << endl;

	// Input/Output/Wire
	for(auto it:varsX) {
		//assert(!depFound[it]); //This is required - in verilog one cannot assign
                               // a value to an input
		if (!depFound [it])	//This is being done temporarily
		//	cout << " A Universal Variable Found UnSAT! " << it << endl;
			ofs << "input " << varNumToName(it) << ";\n";
	}
	for(auto it:varsY) {
		if(!depFound[it])
			ofs << "input " << varNumToName(it) << ";\n";
	}
	ofs << "output o_1;\n";
	for(auto it:varsX) {	//Temporary fix - the qdimacs generation should be fixed!
		if(depFound[it])
			ofs << "wire " << varNumToName(it) << ";\n";
	}
	for(auto it:varsY) {
		if(depFound[it])
			ofs << "wire " << varNumToName(it) << ";\n";
	}

	// Extra wires required for non-tseitin clauses
	int numNonTseitin = 0;
	for(int i = 0; i < allClauses.size(); i++) {
		if(!tseitinClauses[i]) {
			numNonTseitin++;
		}
	}
	assert(numNonTseitin > 0);
	for(int i = 1; i<2*numNonTseitin; i++) {
		ofs << "wire " << extraNumToName(i) << ";\n";
	}


	// Assign Dependencies
	// constants
	for(auto it: depCONST) {
		int var = abs(it);
		bool pos = it>0;
		ofs << "assign " << varNumToName(var) << " = " << (pos?1:0) << ";\n";
	}
	// and
	for(auto&it: depAND) {
		int var = abs(it.first); 
		bool pos = it.first>0;
		string res = vecToVerilogLine(it.second,"&");
		ofs << "assign " << varNumToName(it.first) << " = " << res << ";\n";
	}
	// or
	for(auto&it: depOR) {
		int var = abs(it.first);
		bool pos = it.first>0;
		string res = vecToVerilogLine(it.second,"|");
		ofs << "assign " << varNumToName(it.first) << " = " << res << ";\n";
	}
	// xor
	for(auto&it: depXOR) {
		int var = abs(it.first);
		bool pos = it.first>0;
		string res = vecToVerilogLine(it.second,"^");
		ofs << "assign " << varNumToName(it.first) << " = " << res << ";\n";
	}

	// Assign Non-tseitin dependencies
	int eNum = 1;
	for(int i = 0; i < allClauses.size(); i++) {
		if(!tseitinClauses[i]) {
			string res = vecToVerilogLine(allClauses[i],"|");
			ofs << "assign " << extraNumToName(eNum) << " = " << res << ";\n";
			eNum++;
		}
	}
	assert(eNum == numNonTseitin+1);

	// Conjunct all Extra Variables (x_1 .. x_numNonTseitin)
	int finalVar =  addFlatClausesToVerilog(ofs, 1, numNonTseitin, eNum);
	assert(finalVar <= 2*numNonTseitin);

	ofs << "assign o_1 = " << extraNumToName(finalVar) << ";\n";
	ofs << "endmodule\n";
	ofs.close();
}

int addFlatClausesToVerilog(ofstream&ofs, int start, int end, int&nextVar) {
	assert(start<=end);
	if(start==end)
		return start;

	int mid = (start+end+1)/2 - 1;
	int v1 = addFlatClausesToVerilog(ofs, start, mid, nextVar);
	int v2 = addFlatClausesToVerilog(ofs, mid+1, end, nextVar);

	string res = extraNumToName(v1) + " & " + extraNumToName(v2);
	ofs << "assign " << extraNumToName(nextVar) << " = " << res << ";\n";
	nextVar++;
	return nextVar-1;
}

void writeVariableFile(string fname) {
	ofstream ofs (fname, ofstream::out);

	cout << "# Y : " << varsY.size() << endl;
	for(auto it:varsY) {
		if(!depFound[it])
		{
			ofs << varNumToName(it) << "\n";
			//cout << "Written " <<  varNumToName(it) << " to " << fname << endl;
		}
	//	else
	//		cout << varNumToName(it) << "is a Tseitin variable" << endl;
	}

	ofs.close();
}

void writeDependenceFile(string fname) {
	ofstream ofs (fname, ofstream::out);
	// Assign Dependencies
	// constants
	for(auto it: depCONST) {
		int var = abs(it);
		bool pos = it>0;
		ofs << varNumToName(var) << " = " << (pos?1:0) << ";\n";
	}
	// and
	for(auto&it: depAND) {
		int var = abs(it.first);
		bool pos = it.first>0;
		string res = vecToVerilogLine(it.second,"&");
		ofs << varNumToName(it.first) << " = " << res << ";\n";
	}
	// or
	for(auto&it: depOR) {
		int var = abs(it.first);
		bool pos = it.first>0;
		string res = vecToVerilogLine(it.second,"|");
		ofs << varNumToName(it.first) << " = " << res << ";\n";
	}
	// xor
	for(auto&it: depXOR) {
		int var = abs(it.first);
		bool pos = it.first>0;
		string res = vecToVerilogLine(it.second,"^");
		ofs << varNumToName(it.first) << " = " << res << ";\n";
	}
	ofs.close();
}

string vecToVerilogLine(vector<int> &v, string op) {
	string res;
	for(auto el:v) {
		if(el > 0)
			res = res + varNumToName(abs(el)) + " " + op + " ";
		else
			res = res + "~" + varNumToName(abs(el)) + " " + op + " ";
	}
	return res.substr(0,res.length()-2-op.length());
}

void writeNonTseitinToQdimacsFile(string fname) {
	ofstream ofs (fname, ofstream::out);

	// Extra wires required for non-tseitin clauses
	int numNonTseitin = 0;
	for(int i = 0; i < allClauses.size(); i++) {
		if(!tseitinClauses[i]) {
			numNonTseitin++;
		}
	}

	ofs << VERILOG_HEADER;
	ofs << "p cnf " << numVars << " " << numNonTseitin+depCONST.size() << endl;

	ofs << "a ";
	for(auto it:varsX) {
		if(!depFound[it])
		ofs << it << " ";
	}
	ofs << 0 << endl;

	ofs << "e ";
	for(auto it:varsY) {
		if(!depFound[it])
			ofs << it << " ";
	}
	ofs << 0 << endl;

	// constants
	for(auto it: depCONST) {
		ofs << it << " 0 \n";
	}

	// Non-tseitin clauses
	for(int i = 0; i < allClauses.size(); i++) {
		if(!tseitinClauses[i]) {
			for(auto el: allClauses[i]) {
				ofs << el << " ";
			}
			ofs << "0\n";
		}
	}

	ofs.close();
}

static inline map<int,int>& getImpliesMap(int lit) {
	return (lit>0)?posImplies[lit]:negImplies[-lit];
}

static inline void addToImpliesMap(map<int,int>&m, int lit, int clauseNum) {
	auto it = m.find(lit);
	if(it == m.end()) {
		m[lit] = clauseNum;
	}
	else if(it->second != clauseNum) { // set clauseNum is redundant
		tseitinClauses[clauseNum] = true;
	}
}

static inline void setConst(int lit) {
	cout << "DEPConst " << lit << endl;
	depFound[abs(lit)] = true;
	depCONST.insert(lit);
	litToPropagate.push(lit);
}

static inline void processBinaryClause(int clauseNum) {
	vector<int>&clause  = allClauses[clauseNum];
	assert(clause.size() == 2);
	int v0 = clause[0];
	int v1 = clause[1];

	map<int,int>& v0_map = getImpliesMap(-v0);
	map<int,int>& v1_map = getImpliesMap(-v1);

	addToImpliesMap(v0_map, v1, clauseNum);
	addToImpliesMap(v1_map, v0, clauseNum);
}

bool checkForCycles() {
	vector<set<int> > graph(numVars+1);

	// Create Graph
	for(auto it: depCONST) {
		int var = abs(it);
		graph[var].insert(0);
	}
	for(auto&it: depAND) {
		int var = abs(it.first);
		for(auto&it2:it.second)
			graph[var].insert(abs(it2));
	}
	for(auto&it: depOR) {
		int var = abs(it.first);
		for(auto&it2:it.second)
			graph[var].insert(abs(it2));
	}
	for(auto&it: depXOR) {
		int var = abs(it.first);
		for(auto&it2:it.second)
			graph[var].insert(abs(it2));
	}

	vector<int> DFS_startTime(numVars+1,-1);
	vector<int> DFS_endTime(numVars+1,-1);
	int DFS_currTime = 0;

	for (int i = 0; i < numVars + 1; ++i) {
		if(DFS_startTime[i] == -1) {
			if(DFS_checkForCycles(graph, i, DFS_startTime, DFS_endTime, DFS_currTime)) {
				cerr << i << endl;
				return true;
			}
		}
	}
	return false;
}

bool DFS_checkForCycles(vector<set<int> >& graph, int node, vector<int>& DFS_startTime, vector<int>& DFS_endTime, int& DFS_currTime) {
	if(DFS_startTime[node] != -1) {
		if(DFS_endTime[node] == -1) {
			// Back Edge
			cout << "Found dependency cycle: ";
			return true;
		}
		else {
			// Cross Edge
			return false;
		}
	}
	// Forward Edge
	DFS_startTime[node] = DFS_currTime++;
	
//If a cycle is present, break it by removing a dependency
	for(auto it:graph[node]) {
		if(DFS_checkForCycles(graph, it, DFS_startTime, DFS_endTime, DFS_currTime)) {
			cout << it << " ";
		if (depAND.find(node) != depAND.end()) {
			cout << "Breaking AND dep " << endl;
			depAND.erase(node);	
		}
		else 
		if (depXOR.find(node) != depXOR.end()) {
			cout << "Breaking XOR dep " << endl;
			depXOR.erase(node);	
		}
		else 
		if (depOR.find(node) != depOR.end()) {
			cout << "Breaking OR dep " << endl;
			depOR.erase(node);	
		}
		}
	}

	DFS_endTime[node] = DFS_currTime++;
	return false;
}

void reduceDependencySizes() {
	for(auto&it: depAND) {
		while(it.second.size() > MAX_DEP_SIZE) {
			int start = 0;
			int end = MAX_DEP_SIZE;
			vector<int> newV;
			while(start<it.second.size()) {
				numVars++;
				varsY.push_back(numVars);
				assert(depFound.size() == numVars);
				depFound.push_back(true);

				depAND[numVars] = vector<int>(it.second.begin()+start,it.second.begin()+end);
				newV.push_back(numVars);

				start = end;
				end = min(start + MAX_DEP_SIZE, (int)it.second.size());
			}
			it.second = newV;
		}
	}
	for(auto&it: depOR) {
		while(it.second.size() > MAX_DEP_SIZE) {
			int start = 0;
			int end = MAX_DEP_SIZE;
			vector<int> newV;
			while(start<it.second.size()) {
				numVars++;
				varsY.push_back(numVars);
				assert(depFound.size() == numVars);
				depFound.push_back(true);

				depOR[numVars] = vector<int>(it.second.begin()+start,it.second.begin()+end);
				newV.push_back(numVars);

				start = end;
				end = min(start + MAX_DEP_SIZE, (int)it.second.size());
			}
			it.second = newV;
		}
	}
	for(auto&it: depXOR) {
		while(it.second.size() > MAX_DEP_SIZE) {
			int start = 0;
			int end = MAX_DEP_SIZE;
			vector<int> newV;
			while(start<it.second.size()) {
				numVars++;
				varsY.push_back(numVars);
				assert(depFound.size() == numVars);
				depFound.push_back(true);

				depXOR[numVars] = vector<int>(it.second.begin()+start,it.second.begin()+end);
				newV.push_back(numVars);

				start = end;
				end = min(start + MAX_DEP_SIZE, (int)it.second.size());
			}
			it.second = newV;
		}
	}
}

/*
Abc_Ntk_t*  getNtk(string pFileName) {
	string cmd, initCmd, varsFile, line;
	Abc_Obj_t* pPi, *pCi;
	set<int> varsX;
	set<int> varsY; // To Be Eliminated
	map<string, int> name2Id;
	int liftVal, cummulativeLift = 0;

	initCmd = "balance; rewrite -l; refactor -l; balance; rewrite -l; \
						rewrite -lz; balance; refactor -lz; rewrite -lz; balance";

	pAbc = Abc_FrameGetGlobalFrame();

	cmd = "read " + pFileName;
	if (CommandExecute(pAbc, cmd)) { // Read the AIG
		return NULL;
	}
//	cmd = fraig?initCmd:"balance";
	if (CommandExecute(pAbc, cmd)) { // Simplify
		return NULL;
	}

	Abc_Ntk_t* pNtk =  Abc_FrameReadNtk(pAbc);
	// Aig_Man_t* pAig = Abc_NtkToDar(pNtk, 0, 0);
	return pNtk;
}

int checkUnateSemAll(Aig_Man_t* FAig, vector<int>&unate) { 
	Aig_ManPrintStats(FAig);

	auto unate_start = std::chrono::steady_clock::now();
	auto unate_end = std::chrono::steady_clock::now();
	auto unate_run_time = std::chrono::duration_cast<std::chrono::microseconds>(unate_end - unate_start).count()/1000000.0;

//Is this required?
//	nodeIdtoN.resize(numOrigInputs);
//	for(int i = 0; i < numX; i++) {
//		nodeIdtoN[varsXF[i] - 1] = i;
//	}
//	for(int i = 0; i < numY; i++) {
//		nodeIdtoN[varsYF[i] - 1] = numX + i;
//	}
	
	cout << " Preparing for semantic unate checks " << endl;
	sat_solver* pSat = sat_solver_new();
	Cnf_Dat_t* SCnf = Cnf_Derive(FAig, Aig_ManCoNum(FAig));
	addCnfToSolver(pSat, SCnf);
	int numCnfVars = SCnf->nVars;
	Cnf_Dat_t* SCnf_copy = Cnf_DataDup(SCnf);
 	Cnf_DataLift (SCnf_copy, numCnfVars);	
	addCnfToSolver(pSat, SCnf_copy);
	int status, numUnate, totalNumUnate = 0;
	assert(unate.size()==numY);
//Equate the X's and Y's. 
 	int x_iCnf, y_iCnf; 
	lit Lits[3];
	for(int i = 0; i < numX; ++i) {
		Lits[0] = toLitCond( SCnf->pVarNums[ varsXF[i]], 0 );
		Lits[1] = toLitCond( SCnf_copy->pVarNums[ varsXF[i]], 1 );
	//	cout << " Adding clause " <<  Lits [0] << " " << Lits [1] << endl;
        	if ( !sat_solver_addclause( pSat, Lits, Lits+2 ) )
            		assert( 0 );
		Lits[0] = toLitCond( SCnf->pVarNums[ varsXF[i]], 1 );
		Lits[1] = toLitCond( SCnf_copy->pVarNums[ varsXF[i]], 0 );
        	if ( !sat_solver_addclause( pSat, Lits, Lits+2 ) )
            		assert( 0 );
	//	cout << " Adding clause " <<  Lits [0] << " " << Lits [1] << endl;
	}

	int cont_Vars[numY]; //control Variables
	for(int i = 0; i < numY; ++i) {
	
		cont_Vars[i] = sat_solver_addvar (pSat);
		Lits[0] = toLitCond( SCnf->pVarNums[ varsYF[i]], 0 );
		Lits[1] = toLitCond( SCnf_copy->pVarNums[ varsYF[i]], 1 );
		Lits[2] = Abc_Var2Lit (cont_Vars[i], 0);
//		cout << " Adding clause for " << i << " "  <<  Lits [0] << " " << Lits [1] << " " << Lits [2] << endl;
        	if ( !sat_solver_addclause( pSat, Lits, Lits+3 ) )
            		assert( 0 );
		Lits[0] = toLitCond( SCnf->pVarNums[ varsYF[i]], 1 );
		Lits[1] = toLitCond( SCnf_copy->pVarNums[ varsYF[i]], 0 );
		Lits[2] = Abc_Var2Lit (cont_Vars[i], 0);
///		cout << " Adding clause for " << i << " "  <<  Lits [0] << " " << Lits [1] << " " << Lits [2] << endl;
        	if ( !sat_solver_addclause( pSat, Lits, Lits+3 ) )
            		assert( 0 );
		if (unate [i] != -1) // Y is already syntactically unate
		{
			//unate[i] = -1;
			//cout << "Adding " << varsYF[i] << " as unate " << unate [i] << endl;
			addVarToSolver(pSat, SCnf->pVarNums[varsYF[i]], unate[i]);
			addVarToSolver(pSat, SCnf_copy->pVarNums[varsYF[i]], unate[i]);
		}
	}
	
	//lit LA[numY+4];
	lit LA[numY+2];

	//cout << "NumCnfVars " <<  numCnfVars << endl;
	//cout << "SCnfVars " <<  SCnf->nVars << endl;
	int coID = getCnfCoVarNum(SCnf, FAig, 0);
	
	Aig_Obj_t * pCo = Aig_ManCo(FAig, 0);
	assert (coID == SCnf->pVarNums[pCo->Id]);

	addVarToSolver(pSat, SCnf->pVarNums[pCo->Id], 1);
	addVarToSolver(pSat, SCnf_copy->pVarNums[pCo->Id], 0);
//	LA[0] = toLitCond( SCnf->pVarNums[pCo->Id],0);	
//	LA[1] = toLitCond(SCnf_copy->pVarNums[pCo->Id],1); //Check whether this is positive or negative	-- assuming 0 is true

	int yIndex;

	do {
		numUnate = 0;
		for (int i = 0; i < numY; ++i)
		{
			yIndex  = SCnf->pVarNums[varsYF[i]];
	//		cout << "Checking @ " << i << " for " << varsYF[i] << " YIndex = " << yIndex << "Unate " << unate [i] << endl;	
			for (int j = 0; j < numY; j++)
			{
				if (j == i)
					LA[2+j] = Abc_Var2Lit (cont_Vars[j], 0);
				else
					LA[2+j] = Abc_Var2Lit (cont_Vars[j], 1);
				//cout << " Control variable " << j   << " is " << LA [4+j] << endl;
			}

			if(unate[i] == -1) {
				// Check if positive unate
				LA[0] = toLitCond(SCnf->pVarNums[varsYF[i]], 1); //check the 0 and 1's
				LA[1] = toLitCond(SCnf_copy->pVarNums[varsYF[i]], 0);
				//cout << "Printing assumptions for pos unate : " << LA [0] << " " << LA [1] << " " << LA [2] << " " << LA [3] << endl;
				status = sat_solver_solve(pSat, LA, LA+2+numY, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0);
				//cout << "Status of sat solver " << status << endl;
				if (status == l_False) {
					unate[i] = 1;
					cout << "Var y" << i << " (" << varsYF[i] << ") is positive unate (semantic)" << endl;
					// sat_solver_push(pSat, toLitCond(SCnf->pVarNums[varsYF[i]],0));
					addVarToSolver(pSat, SCnf->pVarNums[varsYF[i]], 1);
					addVarToSolver(pSat, SCnf_copy->pVarNums[varsYF[i]], 1);
					numUnate++;
				}
			}
			if(unate[i] == -1) {
				// Check if negative unate
				LA[0] = toLitCond(SCnf->pVarNums[varsYF[i]], 0); //check the 0 and 1's
				LA[1] = toLitCond(SCnf_copy->pVarNums[varsYF[i]], 1);
				//cout << "Printing assumptions for neg unate : " << LA [0] << " " << LA [1] << " " << LA [2] << " " << LA [3] << endl;
				//LA[0] = toLitCond(getCnfCoVarNum(SCnf, FAig, negUnates[i]),1);
				status = sat_solver_solve(pSat, LA, LA+2+numY, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0);
				//cout << "Status of sat solver " << status << endl;
				if (status == l_False) {
					cout << "Var y" << i << " (" << varsYF[i] << ") is negative unate (semantic)" << endl;
					unate[i] = 0;
					// sat_solver_push(pSat, toLitCond(SCnf->pVarNums[varsYF[i]],1));
					addVarToSolver(pSat, SCnf->pVarNums[varsYF[i]], 0);
					addVarToSolver(pSat, SCnf_copy->pVarNums[varsYF[i]], 0);
					numUnate++;
				}
			}
		}
		cout << "Found " << numUnate << " unates" << endl;
		totalNumUnate += numUnate;

		unate_end = std::chrono::steady_clock::now();
		unate_run_time = std::chrono::duration_cast<std::chrono::microseconds>(unate_end - main_time_start).count()/1000000.0;
		if(numUnate > 0 and unate_run_time >= options.unateTimeout) {
			cout << "checkUnateSemanticAll Timed Out" << endl;
			break;
		}
	}
	while(numUnate > 0);

	sat_solver_delete(pSat);
	Cnf_DataFree(SCnf);
	Cnf_DataFree(SCnf_copy);

//	cout << "TotalNumUnate =  " << totalNumUnate << endl;
	return totalNumUnate;

}

*/

/*
findUnates (char *pFileName)
{
    Cnf_Data_t* SCnf = Cnf_DataReadFromFile(pFileName);
	sat_solver* pSat = sat_solver_new();
	addCnfToSolver(pSat, SCnf);
	int numCnfVars = SCnf->nVars;
	Cnf_Dat_t* SCnf_copy = Cnf_DataDup(SCnf);
 	Cnf_DataLift (SCnf_copy, numCnfVars);	
	addCnfToSolver(pSat, SCnf_copy);
	int status, numUnate, totalNumUnate = 0;
    int Var1; Var2;

    for (int i = 0; i < varsX.size (); i++)
    {
        lit Lits[3];
        Var1 = Scnf->pVarNums[varsX[i]];
        Var2 = Scnf_copy->pVarNums[varsX[i]];
        cout << "Var 1 : " << Var1 << "Var2 " << Var2 << endl;
        Lits[0] = Abc_Var2Lit(Var1-1, 0);
        Lits[1] = Abc_Var2Lit(-Var2-1, 1);
       	if ( !sat_solver_addclause( pSat, Lits, Lits+2 ) )
           		assert( 0 );

        Lits[0] = Abc_Var2Lit(Var2-1, 0);
        Lits[1] = Abc_Var2Lit(-Var1-1, 1);
       	if ( !sat_solver_addclause( pSat, Lits, Lits+2 ) )
           		assert( 0 );

    }

	int cont_Vars[numY]; //control Variables
	for(int i = 0; i < numY; ++i) {
	
		cont_Vars[i] = sat_solver_addvar (pSat);
        Var1 = Scnf->pVarNums[varsY[i]];
        Var2 = Scnf_copy->pVarNums[varsY[i]];
        Lits[0] = Abc_Var2Lit(Var1-1, 0);
        Lits[1] = Abc_Var2Lit(-Var2-1, 1);
		Lits[2] = Abc_Var2Lit (cont_Vars[i], 0);
//		cout << " Adding clause for " << i << " "  <<  Lits [0] << " " << Lits [1] << " " << Lits [2] << endl;
        	if ( !sat_solver_addclause( pSat, Lits, Lits+3 ) )
            		assert( 0 );
        Var1 = Scnf->pVarNums[varsY[i]];
        Var2 = Scnf_copy->pVarNums[varsY[i]];
		Lits[2] = Abc_Var2Lit (cont_Vars[i], 0);
///		cout << " Adding clause for " << i << " "  <<  Lits [0] << " " << Lits [1] << " " << Lits [2] << endl;
       	if ( !sat_solver_addclause( pSat, Lits, Lits+3 ) )
            		assert( 0 );
		if (unate [i] != -1) // Y is already syntactically unate
		{
			//unate[i] = -1;
			//cout << "Adding " << varsYF[i] << " as unate " << unate [i] << endl;
			addVarToSolver(pSat, SCnf->pVarNums[varsYF[i]], unate[i]);
			addVarToSolver(pSat, SCnf_copy->pVarNums[varsYF[i]], unate[i]);
		}
	}
	
	//lit LA[numY+4];
	lit LA[numY+2];

	//cout << "NumCnfVars " <<  numCnfVars << endl;
	//cout << "SCnfVars " <<  SCnf->nVars << endl;
	int coID = getCnfCoVarNum(SCnf, FAig, 0);
	
	Aig_Obj_t * pCo = Aig_ManCo(FAig, 0);
	assert (coID == SCnf->pVarNums[pCo->Id]);

	addVarToSolver(pSat, SCnf->pVarNums[pCo->Id], 1);
	addVarToSolver(pSat, SCnf_copy->pVarNums[pCo->Id], 0);
//	LA[0] = toLitCond( SCnf->pVarNums[pCo->Id],0);	
//	LA[1] = toLitCond(SCnf_copy->pVarNums[pCo->Id],1); //Check whether this is positive or negative	-- assuming 0 is true

	int yIndex;

	do {
		numUnate = 0;
		for (int i = 0; i < numY; ++i)
		{
			yIndex  = SCnf->pVarNums[varsYF[i]];
	//		cout << "Checking @ " << i << " for " << varsYF[i] << " YIndex = " << yIndex << "Unate " << unate [i] << endl;	
			for (int j = 0; j < numY; j++)
			{
				if (j == i)
					LA[2+j] = Abc_Var2Lit (cont_Vars[j], 0);
				else
					LA[2+j] = Abc_Var2Lit (cont_Vars[j], 1);
				//cout << " Control variable " << j   << " is " << LA [4+j] << endl;
			}

			if(unate[i] == -1) {
				// Check if positive unate
				LA[0] = toLitCond(SCnf->pVarNums[varsYF[i]], 1); //check the 0 and 1's
				LA[1] = toLitCond(SCnf_copy->pVarNums[varsYF[i]], 0);
				//cout << "Printing assumptions for pos unate : " << LA [0] << " " << LA [1] << " " << LA [2] << " " << LA [3] << endl;
				status = sat_solver_solve(pSat, LA, LA+2+numY, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0);
				//cout << "Status of sat solver " << status << endl;
				if (status == l_False) {
					unate[i] = 1;
					cout << "Var y" << i << " (" << varsYF[i] << ") is positive unate (semantic)" << endl;
					// sat_solver_push(pSat, toLitCond(SCnf->pVarNums[varsYF[i]],0));
					addVarToSolver(pSat, SCnf->pVarNums[varsYF[i]], 1);
					addVarToSolver(pSat, SCnf_copy->pVarNums[varsYF[i]], 1);
					numUnate++;
				}
			}
			if(unate[i] == -1) {
				// Check if negative unate
				LA[0] = toLitCond(SCnf->pVarNums[varsYF[i]], 0); //check the 0 and 1's
				LA[1] = toLitCond(SCnf_copy->pVarNums[varsYF[i]], 1);
				//cout << "Printing assumptions for neg unate : " << LA [0] << " " << LA [1] << " " << LA [2] << " " << LA [3] << endl;
				//LA[0] = toLitCond(getCnfCoVarNum(SCnf, FAig, negUnates[i]),1);
				status = sat_solver_solve(pSat, LA, LA+2+numY, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0);
				//cout << "Status of sat solver " << status << endl;
				if (status == l_False) {
					cout << "Var y" << i << " (" << varsYF[i] << ") is negative unate (semantic)" << endl;
					unate[i] = 0;
					// sat_solver_push(pSat, toLitCond(SCnf->pVarNums[varsYF[i]],1));
					addVarToSolver(pSat, SCnf->pVarNums[varsYF[i]], 0);
					addVarToSolver(pSat, SCnf_copy->pVarNums[varsYF[i]], 0);
					numUnate++;
				}
			}
		}
		cout << "Found " << numUnate << " unates" << endl;
		totalNumUnate += numUnate;

		unate_end = std::chrono::steady_clock::now();
		unate_run_time = std::chrono::duration_cast<std::chrono::microseconds>(unate_end - main_time_start).count()/1000000.0;
		if(numUnate > 0 and unate_run_time >= options.unateTimeout) {
			cout << "checkUnateSemanticAll Timed Out" << endl;
			break;
		}
	}
	while(numUnate > 0);

	sat_solver_delete(pSat);
	Cnf_DataFree(SCnf);
	Cnf_DataFree(SCnf_copy);

//	cout << "TotalNumUnate =  " << totalNumUnate << endl;
	return totalNumUnate;

}

*/

