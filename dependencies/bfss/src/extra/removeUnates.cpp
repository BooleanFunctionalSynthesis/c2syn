#include "helper.h"
#include "nnf.h"

#define ABC_NAMESPACE NS_ABC

using namespace std;

Abc_Ntk_t* getNtk(string pFileName);

// Abc_Frame_t* pAbc;

vector<int> varsSInv;
vector<int> varsXF, varsXS;
vector<int> varsYF, varsYS; // to be eliminated
int numOrigInputs = 0, numX = 0, numY = 0;
vector<string> varsNameX, varsNameY;
Abc_Frame_t* pAbc = NULL;
sat_solver* m_pSat = NULL;
Cnf_Dat_t* m_FCnf = NULL;
lit m_f = 0;
double sat_solving_time = 0;
double verify_sat_solving_time = 0;
double reverse_sub_time = 0;
chrono_steady_time helper_time_measure_start = TIME_NOW;
chrono_steady_time main_time_start = TIME_NOW;



void getUnates(vector<int> & unate, Aig_Man_t* FAig);
void updateQdmFile(string qdmFileName, set<int> unateVarNums);

void getCONSTUnates(string fname, set<int> & unateVarNums);

int main(int argc, char * argv[]) {
	char * qdFileName;
    if ( argc < 2 ) {
        cout << "Wrong number of command-line arguments. Usage: readCnf qdimacs_filename " << endl;
        return 1;
    }
    qdFileName = argv[1];

	string baseFileName(qdFileName);
	baseFileName = baseFileName.substr(baseFileName.find_last_of("/") + 1);  //Get the file name;
	baseFileName.erase(baseFileName.find (".qdimacs"), string::npos); //This contains the code for the raw file name;
	cout << "BaseName:     " << baseFileName << endl;

	string varFileName = baseFileName + "_var.txt";
	string aigFileName = baseFileName + ".v" ;
	string depFileName = baseFileName + "_dep.txt" ;
	string qdmFileName = baseFileName + ".qdimacs.noUnates" ;
	string noUnaryFile = baseFileName + "_const_dept.txt";

	
	string replicateFile = "cp "+string(qdFileName) + " "+ qdmFileName;
	const char * command = replicateFile.c_str();

	system(command);

	int numUnates = 0;

	map<string, int> name2IdF;
	map<int, string> id2NameF;

	int iterations =0 ;

	while(1) {
		iterations++;
		string readCnf = "/home/rakeshmistry/bin/jatin/bfss_package/bin/readCnf " + qdmFileName;
		system(readCnf.c_str());
		Abc_Ntk_t* FNtk = getNtk(aigFileName);
		Aig_Man_t* FAig = Abc_NtkToDar(FNtk, 0, 0);

		Aig_ManCleanup(FAig);

		varsXF.clear();
		varsYF.clear();
		name2IdF.clear();
		id2NameF.clear();

		vector<string> varOrder;

		cout << "populateVars" << endl;
		populateVars(FNtk, varFileName, varOrder,
						varsXF, varsYF,
						name2IdF, id2NameF);

		cout<<"numX: "<<numX<<" numY: "<<numY<<endl;
		vector<int> unates;

		getUnates(unates, FAig);
		
		set<int> unateVarNums;

		for(int i=0; i<numY; i++) {
		
			string varName = id2NameF[varsYF[i]];
			int varNum =  stoi(varName.substr(2));

			if(unates[i]==1) { 
				unateVarNums.insert(varNum);
				cout<<"unate: "<<varNum<<endl;
			}

			else if(unates[i]==0){		
				unateVarNums.insert(-varNum);
				cout<<"unate: "<<(-varNum)<<endl;
			}
		}

		cout<<"ITERATION#: "<<iterations<<" numY: "<<numY<<" numUnates "<<unateVarNums.size()<<endl;
		getCONSTUnates(noUnaryFile, unateVarNums);

		if(numY==0)
			cout<<"solved using preprocessing"<<endl;
		if(unateVarNums.empty())
			break;
		
		updateQdmFile(qdmFileName, unateVarNums);
		 //break;

	}

	cout<<"#iterations: "<<iterations<<endl;
	return 0;


}



void getCONSTUnates(string fname, set<int> & unateVarNums) {
	int tmpVar;
	cout<<"fileName: "<<fname<<endl;

	
 
	FILE *qdFPtr = fopen (fname.c_str(), "r");	
	cout<<"file openend"<<endl; 
	while (fscanf(qdFPtr, "%d", &tmpVar)!=EOF) { 
		cout<<"reading "<<tmpVar<<endl;
		if(tmpVar!=0)
			unateVarNums.insert(tmpVar);

	}
	 fclose (qdFPtr);
}

void updateQdmFile(string qdmFileName, set<int> unateVarNums) {
    char C[100], c;
    int tmpVar;

    char header1[1000], header2[1000000], header3[1000000];


	FILE *qdFPtr = fopen (qdmFileName.c_str(), "r");

	int numVars, numClauses;
	// Number of variables and clauses
	fscanf (qdFPtr, "%c", &c);
	fscanf (qdFPtr, "%s", C);
	while (strcmp (C, "cnf") != 0)
		fscanf (qdFPtr, "%s", C);
	fscanf(qdFPtr, "%d %d", &numVars, &numClauses); // read first line p cnf
	cout << "old numVars:       " <<  numVars << endl;
	cout << "old numClauses:   " << numClauses << endl;
	
	

	assert(numVars!=0);
	assert(numClauses!=0);

	 vector<int> varsXQ, varsYQ;
	// // Vars X
	fscanf (qdFPtr, "%c", &c);
	while (c != 'a')
		fscanf (qdFPtr, "%c", &c);
	fscanf(qdFPtr, "%d", &tmpVar);
	while (tmpVar !=0) {
		varsXQ.push_back(tmpVar);
		fscanf(qdFPtr, "%d", &tmpVar);
	}
	// cout << "varsXQ.size(): " << varsXQ.size() << endl;
	// assert (numVars > varsXQ.size());

// 	assert(fgets(header2, 1000000, qdFPtr)!=NULL);
	// // Vars Y (to elim)

	
	fscanf (qdFPtr, "%c", &c);
	while (c != 'e')
		fscanf (qdFPtr, "%c", &c);
	
	fscanf(qdFPtr, "%d", &tmpVar);
	while (tmpVar !=0) {
	 	varsYQ.push_back(tmpVar);
	 	fscanf(qdFPtr, "%d", &tmpVar);
	 }
	
	while (c != '\n')
                fscanf (qdFPtr, "%c", &c);
	// cout << "varsYQ.size(): " << varsYQ.size() << endl;
	// assert (numVars > varsYQ.size());

		

	//assert(fgets(header3, 1000000, qdFPtr)!=NULL);
//	cout<<header2;
//	cout<<header3;
//
	map<int, int> newVarMapping;
	numVars-=unateVarNums.size();

	auto unIndex = unateVarNums.begin();
	for(int j=0; j<unateVarNums.size(); j++) {
		int varN = numVars+1+j;
		if(unateVarNums.find(varN)!=unateVarNums.end() || unateVarNums.find(-varN)!=unateVarNums.end())
			continue;
		while(abs(*unIndex) > numVars)
			unIndex++;
		newVarMapping[varN] = abs(*unIndex);		
		unIndex++;
	}
	for(auto q: newVarMapping) {
		cout<<q.first<<" is mapped to "<<q.second<<endl;
	}
	//assert(unIndex==unateVarNums.end());	
	
	vector<vector<int> > clauses;

	int newNumClauses = 0;
	while (fscanf(qdFPtr, "%d", &tmpVar)!=EOF) {

		bool skipClause = false;
		vector<int> tempClause;

		while (tmpVar != 0) {
			bool skipVar = false;

			if(unateVarNums.find(tmpVar)!=unateVarNums.end()) {
				skipClause = true;
			}	

			else if(unateVarNums.find(-tmpVar)!=unateVarNums.end()) {
				skipVar = true;
			}
			
			if(!skipVar){
				bool sign = tmpVar>0;
				if(abs(tmpVar)>numVars){
					tmpVar=newVarMapping[abs(tmpVar)];
					tmpVar=sign?tmpVar:-tmpVar;
				}
				tempClause.push_back(tmpVar);
			}
			fscanf(qdFPtr, "%d", &tmpVar);
		}

		if(!tempClause.empty() and !skipClause) {
			clauses.push_back(tempClause);
		}

	}
	fclose (qdFPtr);


	
	ofstream ofs (qdmFileName);

	ofs<<"p cnf "<<numVars<<" "<<clauses.size()<<endl;
	// cout<<header1;
//	ofs<<header2;
	ofs<<"a ";
	for(auto varY: varsXQ){
		if(varY>numVars)
                        varY=newVarMapping[varY];
             ofs<<varY<<" ";
        }
        ofs<<"0\n";
	ofs<<"e ";
	for(auto varY :  varsYQ) {
		if(unateVarNums.find(varY)!=unateVarNums.end() || unateVarNums.find(-varY)!=unateVarNums.end())
			continue;
		if(varY>numVars)
			varY=newVarMapping[varY];
		ofs<<varY<<" ";
	}
	ofs<<"0\n";	
	//ofs<<header3;

	for(auto cl: clauses) {
		for(auto var: cl) {
			ofs<<var<<" ";
		}
		ofs<<"0\n";	
	}

	ofs.close();
	cout<<"completed"<<endl;
}



void getUnates(vector<int> & unate, Aig_Man_t* FAig) {
		unate.resize(numY, -1);

		int n, numSynUnates = 0;
		while((n = checkUnateSyntacticAll(FAig, unate)) > 0) {
				substituteUnates(FAig, unate);
				numSynUnates += n;
			}

		cout << "Syntactic Unates Done" << endl;
		int numSemUnates = 0;

		numSemUnates = checkUnateSemAll (FAig, unate);
		substituteUnates(FAig, unate);

		cout << "Total Syntactic Unates: " << numSynUnates << endl;
		cout << "Total Semantic  Unates: " << numSemUnates << endl;
}

Abc_Ntk_t*  getNtk(string pFileName) {
	string cmd, initCmd;

	initCmd = "balance; rewrite -l; refactor -l; balance; rewrite -l; \
						rewrite -lz; balance; refactor -lz; rewrite -lz; balance";

	pAbc = Abc_FrameGetGlobalFrame();

	cmd = "read " + pFileName;
	if (CommandExecute(pAbc, cmd)) { // Read the AIG
		return NULL;
	}
	cmd = initCmd;
	if (CommandExecute(pAbc, cmd)) { // Simplify
		return NULL;
	}

	Abc_Ntk_t* pNtk =  Abc_FrameReadNtk(pAbc);
	// Aig_Man_t* pAig = Abc_NtkToDar(pNtk, 0, 0);
	return pNtk;
}

