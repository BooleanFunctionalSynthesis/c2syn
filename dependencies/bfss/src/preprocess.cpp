#include "helper.h"
#include "nnf.h"
#include "synNNF.h"

#define ABC_NAMESPACE NS_ABC

using namespace std;

extern void readQdimacsFile(char * );
extern int preprocess(set<int> & );
extern void writeOutput(char *);
//extern void writeOutput(char *, bool);

Abc_Ntk_t* getNtk(string pFileName);
void getUnates(vector<int> & unate, Aig_Man_t* FAig);

//vector<int> varsX;
//vector<int> varsY;
vector<int> varsXF, varsXS;
vector<int> varsYF, varsYS; // to be eliminated
int numOrigInputs = 0, numX = 0, numY = 0;
int numSolved = 0; //This tells us how many variables are currently in SynNNF

vector<string> varsNameX, varsNameY;
Abc_Frame_t* pAbc = NULL;
sat_solver* m_pSat = NULL;
Cnf_Dat_t* m_FCnf = NULL;
lit m_f = 0;
//sat_solver* pSat = NULL;
//Cnf_Dat_t* pCnf = NULL;
//lit l_p = 0;
double sat_solving_time = 0;
double verify_sat_solving_time = 0;
double reverse_sub_time = 0;
chrono_steady_time helper_time_measure_start = TIME_NOW;
chrono_steady_time main_time_start = TIME_NOW;

vector<vector<int>> clauses;
vector<int> unate;

synSolver syn;

int main(int argc, char * argv[]) {
	char * qdFileName;
    if ( argc < 2 ) {
        cout << "Wrong number of command-line arguments. Usage: pre_process qdimacs_filename " << endl;
        
        return 1;
    }
    qdFileName = argv[1];

	string baseFileName(qdFileName);
	baseFileName = baseFileName.substr(baseFileName.find_last_of("/") + 1);  //Get the file name;
	baseFileName.erase(baseFileName.find (".qdimacs"), string::npos); //This contains the code for the raw file name;
	cout << "BaseName:     " << baseFileName << endl;

   // string noUnaryFile = baseFileName + ".qdimacs.noUnary" ;
	string aigFileName = baseFileName + ".v" ;
	string varFileName = baseFileName + "_var.txt";
//Preprocessing round 0 - Find unary variables and simplify and also  << varfind Tseitin variables.

    readQdimacsFile(qdFileName); 
    set<int> unateVarNums;


    preprocess (unateVarNums); //Do unate check even if no tseitin's found
    writeOutput (qdFileName); //Do not write the preprocessed qdimacs file.
    
    bool moreUnates = true;

  	map<string, int> name2IdF;
  	map<int, string> id2NameF;
	vector<string> varOrder;

    while (moreUnates)
    {

        Abc_Ntk_t* FNtk = getNtk(aigFileName);
        Aig_Man_t* FAig = Abc_NtkToDar(FNtk, 0, 0);

	    Aig_ManCleanup(FAig);

        varsXF.clear();
        varsYF.clear();
        name2IdF.clear();
        id2NameF.clear();
        varOrder.clear();


	    cout << "populateVars" << endl;
	    populateVars(FNtk, varFileName, varOrder, varsXF, varsYF, name2IdF, id2NameF);

	    cout<<"numX: " << numX << " numY: " << numY << endl;

        unate.resize(numY);
        for (int index = 0; index < numY; index++)
            unate[index] = -1;

	    getUnates(unate, FAig);

        unateVarNums.clear();

	    for(int index=0; index < numY; index++) {
		
		string varName = id2NameF[varsYF[index]];
		int varNum =  stoi(varName.substr(2));

		if(unate[index]==1) { 
    		unateVarNums.insert(varNum);
			//	cout<<"unate: "<<varNum<<endl;
             //   ofs << varNum << " 0 " << endl;
	    }

		else if(unate[index]==0){		
			unateVarNums.insert(-varNum);
            //ofs << -varNum << " 0 " << endl;
			//cout<<"unate: "<<(-varNum)<<endl;
	    	}
	    }

       // for (set<int>::iterator it  = unateVarNums.begin(); it != unateVarNums.end(); it++)
        //    cout << "Unate" << *it;
        //cout << endl;
       // bool cont = false;

        if (unateVarNums.size() == 0 )
        {
            moreUnates = false;
            writeOutput (qdFileName); //THe unates are not reflected in the verilog file until they are preprocessed.
            cout << "End of preprocessing. ";
            break; 
        }
        else if( unateVarNums.size() == numY)
        {
                cout << "End of preprocessing. ALL variables UNATE!" << endl;
                cout << endl;
                preprocess (unateVarNums);
                writeOutput (qdFileName); //process the unates and simplify the qdimacs file.
                break;
        }
        else
        {
            bool cont = preprocess (unateVarNums);
            writeOutput (qdFileName); //Do not write the preprocessed qdimacs file.
            if (! cont) //No more tseitins discovered; 
             break;
            
        }

    }

    syn.init ();
    syn.createSyn
    //ofs.close();
//write Unate variables to the qdimacs file

}

/*
void readCnfNoUnary (char * qdFileName)
{

	readQdimacsFile(qdFileName);
	cout << "Finished readQdimacsFile" << endl;

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
			if(tmpVar > 0) { // pos
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
*/

void getUnates(vector<int> & unate, Aig_Man_t* FAig) {
        options.unateTimeout = 2000;
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

