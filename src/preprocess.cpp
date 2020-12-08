#include "helper.h"
#include "synNNF.h"
#include "readCnf.h"

#define ABC_NAMESPACE NS_ABC
#define MAX_CLAUSE_SIZE = 100;


using namespace std;

extern vector<int> varsX;
extern vector<int> varsY;
extern vector<int> origVarsY;
extern vector<int> tseitinVars;
extern vector<bool> tseitinClauses;
extern map<int, vector<int> > depAND;
extern map<int, vector<int> > depOR;
extern map<int, vector<int> > depXOR;
extern set<int> depCONST;

extern void readQdimacsFile(char * );
extern int preprocess(set<int> & );
extern void writeOutput(char *);
extern Aig_Obj_t* Aig_SubstituteVec(Aig_Man_t* pMan, Aig_Obj_t* initAig, vector<int> varIdVec,
	vector<Aig_Obj_t*>& funcVec);

extern void printAig(Aig_Man_t* pMan);
extern void print (vector <int> &);
extern vector<Aig_Obj_t *> Aig_SupportVec(Aig_Man_t* pMan, Aig_Obj_t* root);
//extern void writeOutput(char *, bool);

Abc_Ntk_t* getNtk(string pFileName);
void getUnates(vector<int> & unate, Aig_Man_t* &FAig);
int checkSemInd (Aig_Man_t* FAig, vector <int>& indX, vector<int>& indY);
int checkSynInd (Aig_Man_t* pMan, vector <int>& indX, vector<int>& indY) ;
//void createFuncT( Aig_Man_t *, map<int, Aig_Obj_t*> &, map<int, int> &);
//Aig_Obj_t* createFuncT( Aig_Man_t* p, map <int, Aig_Obj_t*> & newYCi, map<int,int> &Ymap,  map<int, vector<int> >& graph, int node, map<int,int>& nodeOp ) ;
void createFuncT(map<int, int>& Ymap, int offset, vector <vector<int> >& funcTClauses);
void CreateDFSGraph(Aig_Man_t* p, map <int, Aig_Obj_t*> & newYCi, map<int,int> &Ymap) ;
void prop5 (Aig_Man_t * p);

//extern vector<int> varsX;
//extern vector<int> varsY;
vector<int> varsXF;
vector<int> varsYF; // to be eliminated
int numOrigInputs = 0, numX = 0, numY = 0;
int numSolved = 0; //This tells us how many variables are currently in SynNNF

//Required due to inclusion of helper.h
vector<string> varsNameX, varsNameY;
Abc_Frame_t* pAbc = NULL;
sat_solver* m_pSat = NULL;
Cnf_Dat_t* m_FCnf = NULL;
lit m_f = 0;
sat_solver* pSat = NULL;
Cnf_Dat_t* pCnf = NULL;
lit l_p = 0;
double sat_solving_time = 0;
double verify_sat_solving_time = 0;
double reverse_sub_time = 0;
chrono_steady_time helper_time_measure_start = TIME_NOW;
chrono_steady_time main_time_start = TIME_NOW;
vector<int> varsXS;
vector<int> varsYS; // to be eliminated
//---------------------
//map< int, int> whichVar ; // Map a varNum to X or Y or T ; X = 0; Y = 1; T = 2
//map<int, int> varIndex; //Map a varnum to index into the varsXF and varsYF vectors

map <int, Aig_Obj_t* > qd2AigMap; //Maps a var in qdimacs to the corresponding Object in AIG.
map <int,  Aig_Obj_t*> funcT;

//vector<vector<int>> clauses;
vector<int> unate;

synSolver s;

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
	string tseitinFileName = baseFileName + "_dep.txt";
//Preprocessing round 0 - Find unary variables and simplify and also  << varfind Tseitin variables.

    cout << tseitinFileName << endl;

    readQdimacsFile(qdFileName); 
    set<int> unateVarNums;

    cout << "NumX = " << varsX.size() << " numY = " << varsY.size() << endl;
    preprocess (unateVarNums); //Do unate check even if no tseitin's found
    writeOutput (qdFileName); //Do not write the preprocessed qdimacs file.
    
    bool moreUnates = true;

  	map<string, int> name2IdF;
  	map<int, string> id2NameF;
	vector<string> varOrder;
    Abc_Ntk_t* FNtk;
    Aig_Man_t* FAig = NULL;
    while (moreUnates)
    {
    cout << " varsX " << endl;
    print (varsX);
    cout << " varsY " << endl;
    print (origVarsY);

        FNtk = getNtk(aigFileName);

        if (FNtk == NULL)
            cout << " Aig File " << aigFileName << " not read " << endl;

        Abc_Obj_t * pObj;
        int i;
       // Abc_NtkForEachObj( FNtk, pObj, i )
        //    cout << " " << Abc_ObjName(pObj);
        cout << endl;
        if (FAig != NULL)
        {
            Aig_ManStop (FAig);
        }
        FAig = Abc_NtkToDar(FNtk, 0, 0);
        assert (FAig != NULL);

	    Aig_ManCleanup(FAig);
        //cout << "Printing AIG before Unate Checks" << endl;
        //printAig( FAig);
        if (FAig == NULL)
            cout << " In while loop : Manager NULL " << endl;

        varsXF.clear();
        varsYF.clear();
        name2IdF.clear();
        id2NameF.clear();
        varOrder.clear();


	    cout << "populateVars" << endl;
	    populateVars(FNtk, varFileName, varOrder, varsXF, varsYF, name2IdF, id2NameF);

        numX = varsXF.size();
        numY = varsYF.size();

	    cout<<"numX: " << numX << " numY: " << numY << endl;

        unate.resize(numY, -1); //Check if unates need to be resized each time or once is enough
        //for (int index = 0; index < numY; index++)
         //   unate[index] = -1;

	    getUnates(unate, FAig);
        //cout << "Printing AIG after Unate Checks" << endl;
        //printAig( FAig);

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
       /* bool cont = false;

        if (unateVarNums.size() == 0)
            moreUnates = false;
        else
            cont = preprocess(unateVarNums);

         if( unateVarNums.size() == numY)
            cont = true;

          writeOutput (qdFileName); 

          if (unateVarNums.size() == 0  && unateVarNums.size() == numY)
                cout << "End of preprocessing.  NumUnates = " << unateVarNums.size() << endl;
         */

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
                exit (1);
            //    break;
        }
        else
        {
            bool cont = preprocess (unateVarNums); //Unates discovered - 
            writeOutput (qdFileName); 
            if (! cont) //No more tseitins discovered; 
             break;
        }
    }

    //Create a mapping between the qdimacs variables and the AIG variables.
	 for(int index=0; index < numX; index++) {
		
            string varName = id2NameF[varsXF[index]];
            int varNum =  stoi(varName.substr(2));

            qd2AigMap[varNum] = Aig_ManObj(FAig, varsXF[index]);
      }
	 for(int index=0; index < numY; index++) {
		
            string varName = id2NameF[varsYF[index]];
            int varNum =  stoi(varName.substr(2));

            //if(unate[index]==1)  
             //   qd2AigMap[varNum] = Aig_ManConst1(FAig);
            //else if(unate[index]==0)  
             //   qd2AigMap[varNum] = Aig_ManConst0(FAig);
            //else
                qd2AigMap[varNum] = Aig_ManObj(FAig, varsYF[index]);
                
      }

   //Also add the X variables to the map 

//    cout << " Creating a mapping between the qdimacs & Aig " << endl;
 //     for (auto it: qd2AigMap)
  //      cout << it.first << " : "  << Aig_ObjId(it.second) << endl ;

    //printAig (FAig);
    vector<int> indX(numX);
    vector<int> indY(numY);
    //Collect leaves in the suport)
    int status;

    if (FAig == NULL)
        cout << "Aig Manager NULL. Check " << endl;

    cout << " Checking for Syntatic Independence " << endl;
    status = checkSynInd(FAig, indX, indY); //
    if (status == -1)
        status = checkSemInd (FAig, indX, indY);

    if (status == 0)
        cout << " F syntactically/semantically independent of X " << endl;
    else if (status == 1)
        cout << " F syntactically/semantically independent of Y " << endl;
        
   //if (status < 0)
     //prop5( FAig);
   // if (status >= 0)
    //{

    
        Aig_ManStop (FAig); //Need to return the SynNNF form here - TODO
    //}
    cout << " Calling the synNNF Solver " << endl;
    cout << " varsX " << endl;
    print (varsX);
    cout << " varsY " << endl;
    print (origVarsY);
    //s.init();
/*    for (auto &it: unateVarNums)
    {
        vector<int> unaryClause; //Unates and Unit clauses add to allClauses
        unaryClause.push_back (it);
        allClauses.push_back(unaryClause);
    }
    */
//Add Unates/Unit Clauses; May lead to some duplication.
    s.CreateSynNNF(allClauses, varsX, origVarsY, tseitinClauses, tseitinVars, baseFileName, depCONST, depAND, depOR, depXOR);
    //s.CreateSynNNF(allClauses, varsX, origVarsY, tseitinClauses); //tseitinVars);
    return status;
    //s.solve (NULL);

    //ofs.close();
//write Unate variables to the qdimacs file

}

void getUnates(vector<int> & unate, Aig_Man_t* &FAig) {
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
    cout << cmd << endl;
	if (CommandExecute(pAbc, cmd)) { // Read the AIG
        cerr<< "Could not read " << pFileName << endl;
		return NULL;
	}
	cmd = initCmd;
    cout << cmd << endl;
	if (CommandExecute(pAbc, cmd)) { // Simplify
        cerr<< "Could not simplify " << pFileName << endl;
		return NULL;
	}

	Abc_Ntk_t* pNtk =  Abc_FrameReadNtk(pAbc);
	// Aig_Man_t* pAig = Abc_NtkToDar(pNtk, 0, 0);
	return pNtk;
}

//This functions implements proposition 5 of the paper.

void prop5 (Aig_Man_t * p)
{

    cout << " In Prop 5" << endl;
    assert (Aig_ManCoNum(p) == 1); //Co should be 1.
    //Create New variables for X and Y for semantic checks
    map <int, Aig_Obj_t *> newYCi;
    map<int, int> Ymap;
    //map <int, Aig_Obj_t *> newXCi;

    //cout << " F " << endl;
   // Aig_ManShow(p, 0, NULL);
   // printAig( p);

	vector<Aig_Obj_t* > funcVec;
	vector<int> varIdVec;
    Aig_Obj_t * pCi;
    
    varIdVec.resize(0);
	funcVec.resize(0);
//    for (int i = 0; i < numX; i++)  //create (Y').
 //   {
       // if (unate[i] == -1) //Y is not unate
        //{
  //          pCi = Aig_ObjCreateCi ( p );
   //         newXCi[i] = pCi;
	//		varIdVec.push_back(varsXF[i]);
	//		funcVec.push_back(pCi);
        //}
   // }
    for (int i = 0; i < numY; i++)  //create (Y').
    {
        if (unate[i] == -1) //Y is not unate
        {
            pCi = Aig_ObjCreateCi ( p );
            newYCi[i] = pCi;
            Ymap[varsYF[i]] = Aig_ObjId(pCi);
			varIdVec.push_back(varsYF[i]);
			funcVec.push_back(pCi);
        }
    }
	Aig_Obj_t* F_prime_Obj = Aig_SubstituteVec(p, Aig_ManCo(p,0), varIdVec, funcVec);
	Aig_Obj_t* F_prime_Co = Aig_ObjCreateCo(p, F_prime_Obj);
    Aig_Obj_t* F_Co = Aig_ManCo(p,0);

    
   // cout << " After creating F_prime " << endl;
   // printAig( p);
    Cnf_Dat_t* FCnf = Cnf_Derive(p, Aig_ManCoNum(p));
	sat_solver *pSat = sat_solver_new();
	addCnfToSolver(pSat,FCnf);

//Add F_Co and \neg F_prime_Co to the solver
    bool allOk = true;
	allOk = allOk && addVarToSolver(pSat, FCnf->pVarNums[F_Co->Id], 1);
    //cout << "Adding " << FCnf->pVarNums[F_Co->Id] << " to the solver " << allOk << endl;
	allOk = allOk && addVarToSolver(pSat, FCnf->pVarNums[F_prime_Co->Id], 0);
    //cout << "Adding " << FCnf->pVarNums[F_prime_Co->Id] << " to the solver " << allOk << endl;
//	vector <vector <lit>> funcTClauses;
 //   createFuncT(Ymap, FCnf->nVars, funcTClauses);
    lit *l;
    int sz = 0;
    cout << "Adding funcT to the SAt Solver " << endl;
    int offset = FCnf->nVars;
    for (int i = 0; i < allClauses.size(); i++)
    {
        if (tseitinClauses[i]) //If the clause is tseitin
        {
            l = new lit[allClauses[i].size()];
            sz = 0;
		    vector<int> tempClause;
            for (auto &it : allClauses[i])
            { 
                lit newVar;

                int var = abs(it);
                bool pos = (it < 0);
                if (qd2AigMap.count (var))
                {
                    Aig_Obj_t* oldci = qd2AigMap[var];
                  //  cout << " Aig for " << var << " is " << oldci->Id << endl;
                    if (Ymap.count(oldci->Id) > 0)
                    {
                        newVar = Ymap [oldci->Id]; //Use Y'
                       // cout << "New Y for " << oldci->Id << " is " << Ymap[oldci->Id] << endl;
                    }
                    else
                    {
                        newVar = oldci->Id; //Keep the same X
                      //  cout << "New X for " << oldci->Id << " is " << Abc_Var2Lit(oldci->Id, 0) << " and " << Abc_Var2Lit(oldci->Id, 1) <<  endl;
                    }
                   l[sz] = toLitCond( FCnf->pVarNums[ newVar], pos);
                //   cout << "Cnf var num for " << newVar << " is " << l[sz] << endl;
                }
                else
                {
                    newVar = var + offset; //For all others- offset the clauses by the number of variables
                   l[sz] = toLitCond(newVar, pos);

                }
             //   cout << "Old var = " << var << " New var = " << newVar << endl;
              //  tempClause.push_back(newVar * (pos? -1 : 1));

                //substitute with new Y
                sz++;
            }
            if(!sat_solver_addclause(pSat, l, l+ sz)) {
                cerr << "Warning: Cannot add clause " << i  << " sat_solver_addclause returned false" << endl;
               // return false;
            }
            delete [] l;
            //for (int j = 0; j < sz; j ++)
             //   cout <<  l[ j] << " " ;
             //cout << endl;
            //print (tempClause);
            //funcTClauses.push_back(tempClause);
        }
     }

	int cont_YVars[numY]; //control Variables
    lit Lits[3];
	for(int i = 0; i < numY; ++i) {
        if (unate[i] == -1) //It is present in the support. Add equality clauses for the Y variables
        {
            cont_YVars[i] = sat_solver_addvar (pSat);
            Lits[0] = toLitCond( FCnf->pVarNums[ varsYF[i]], 0 );
            Lits[1] = toLitCond( FCnf->pVarNums[ Ymap[varsYF[i]]], 1 );
            Lits[2] = Abc_Var2Lit (cont_YVars[i], 0);
    	//	cout << " Adding clause for " << i << " "  <<  Lits [0] << " " << Lits [1] << " " << Lits [2] << endl;
                if ( !sat_solver_addclause( pSat, Lits, Lits+3 ) )
                        assert( 0 );
            Lits[0] = toLitCond( FCnf->pVarNums[ varsYF[i]], 1 );
            Lits[1] = toLitCond( FCnf->pVarNums[ Ymap[varsYF[i]]], 0 );
            Lits[2] = Abc_Var2Lit (cont_YVars[i], 0);
    	//	cout << " Adding clause for " << i << " "  <<  Lits [0] << " " << Lits [1] << " " << Lits [2] << endl;
                if ( !sat_solver_addclause( pSat, Lits, Lits+3 ) )
                        assert( 0 );
         }
	}
    //Everything in! Now solve for each variable

    int yIndex = 0;
    lit LA [numY];
    int status;
    for (int i = 0; i < numY; ++i)
	{
            if (unate[i] == -1)
            {
                yIndex = 2;
			    for (int j = 0; j < numY; j++)
			    {
                    if (unate[j] == -1)
                    {
                    //Add the control variables
                        if (j == i)
                            LA[yIndex++] = Abc_Var2Lit (cont_YVars[j], 0);
                        else
                            LA[yIndex++] = Abc_Var2Lit (cont_YVars[j], 1);
                    }
                }
                for (int k = 0; k < 2; k++)
                {
                       //cout << " k = " << k << endl;
                       LA[0] = toLitCond(FCnf->pVarNums[varsYF[i]], k);
                       LA[1] = toLitCond(FCnf->pVarNums[Ymap[varsYF[i]]], (k+1)%2);
               //        if (k == 1 && i == 0)
                 //               Sat_SolverWriteDimacs (pSat, "funcT.qdimacs", LA, LA+yIndex, 0);
                    //cout << " Control variable " << j   << " is " << LA [4+j] << endl;
                       status = sat_solver_solve(pSat, LA, LA+yIndex, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0);
                       if (status == l_False) {
                                cout << "Theta check for Var y" << i << " (" << varsYF[i] << " = " << k << ") is True " << endl;
                       }
                       else
                       {
                              if (status == l_True)
                                    cout << "Theta check for Var y" << i << " (" << varsYF[i] << " = "  << k << ") is False " << endl;
                                
                          
                       }
                }
           }	
     }
}

void createFuncT(map<int, int>& Ymap, int offset, vector <vector<lit> >& funcTClauses)
{

    for (int i = 0; i < allClauses.size(); i++)
    {
        if (tseitinClauses[i]) //If the clause is tseitin
        {
		    vector<int> tempClause;
            for (auto &it : allClauses[i])
            { 
                lit newVar;

                int var = abs(it);
                bool pos = (it < 0);
                if (qd2AigMap.count (var))
                {
                    Aig_Obj_t* oldci = qd2AigMap[var];
                    //cout << " Aig for " << var << " is " << oldci->Id << endl;
                    if (Ymap.count(oldci->Id) > 0)
                    {
                        newVar = Ymap [oldci->Id]; //Use Y'
                       // cout << "New Y for " << oldci->Id << " is " << Ymap[oldci->Id] << endl;
                    }
                    else
                    {
                        newVar = oldci->Id; //Keep the same X
                      //  cout << "New X for " << oldci->Id << " is " << Abc_Var2Lit(oldci->Id, 0) << " and " << Abc_Var2Lit(oldci->Id, 1) <<  endl;
                    }
                
                }
                else
                {
                    newVar = var + offset; //For all others- offset the clauses by the number of variables

                }
             //   cout << "Old var = " << var << " New var = " << newVar << endl;
                tempClause.push_back(newVar * (pos? -1 : 1));

                //substitute with new Y
            }
            print (tempClause);
            funcTClauses.push_back(tempClause);
        }
     }
}
//Copied from readCnf.cpp - checkForCycles. Modified the code for FuncT creation
void CreateDFSGraph(Aig_Man_t* p, map <int, Aig_Obj_t*> & newYCi, map<int,int> &Ymap) {
	map<int, vector <int>  > graph;
	map< int, int> nodeOp;

	// Create Graph
//	for(auto it: depCONST) {
//		int var = abs(it);
//		graph[var].insert(0);
//}
	for(auto&it: depAND) {
		int var = abs(it.first);
	//	for(auto&it2:it.second)
			graph[var] = it.second;
        nodeOp[var] = 1;
	}
	for(auto&it: depOR) {
		int var = abs(it.first);
		//for(auto&it2:it.second)
			graph[var] = it.second;
        nodeOp[var] = 2;
	}
	for(auto&it: depXOR) {
		int var = abs(it.first);
		//for(auto&it2:it.second)
			graph[var] = it.second;
        nodeOp[var] = 3;
	}
 //   cout << "Before FuncT " << endl;
  //  printAig(p);

	for (auto &it: graph)
    {
        int var = it.first;
       // if ( funcT.count(var) == 0) //Not Already processed
        //    funcT[var] = createFuncT(p, newYCi, Ymap, graph, var, nodeOp);            
	}
    Aig_Obj_t *pObj, *temp, *res;

    set<Aig_Obj_t*> funcTnodes;

    for (auto &it: funcT)
    {
        int var = it.first;
       funcTnodes.insert(it.second);

    }
    res = Aig_ManConst1(p);
    for (auto &it: funcTnodes)
    {
         pObj = it;
         cout << "Anding node " << Aig_ObjId(Aig_Regular(pObj)) << endl;
         res = Aig_And (p, pObj, temp = res);
         cout << "Id of res is " << Aig_ObjId(Aig_Regular(res)) << endl;

    }
    Aig_ObjCreateCo(p, res);
    //printAig(p);
}
//	return false;

/*Aig_Obj_t* createFuncT( Aig_Man_t* p, map <int, Aig_Obj_t*> & newYCi, map<int,int> &Ymap,  map<int, vector<int> >& graph, int node, map<int,int>& nodeOp ) {


    Aig_Obj_t * rhs2, *rhs1, *temp, *temp1;
//	for(auto it:rhses) {

        int op = nodeOp[node];
        rhs2 = NULL;
//Nodes should have been defined
        int secVar = 0;
        for (auto &secIt : graph[node])
        {
            secVar = abs (secIt);

	        bool pos = secVar < 0;

          //  cout << " var " << node <<  "Secvar " << secVar << " " << qd2AigMap.count(secVar)<< endl;
            if (qd2AigMap.count(secVar)) //Is it a leaf?
            {
                temp1 = qd2AigMap[secVar];

                if (Ymap.count(Aig_ObjId(temp1))) //Get the Y'
                    temp1 = Aig_ManObj(p, Ymap[Aig_ObjId(temp1)]);

                //cout << "from qd2AigMap " << endl;
                //Aig_ObjPrintVerbose(Aig_Regular(temp1), 1);
                //cout << endl;

            }
                
            else 
            {
                if (funcT.count(secVar)) // Has it been created already
                {
                        temp1 = funcT[secVar];
                 //       cout << "from funcT " << endl;
                  //      Aig_ObjPrintVerbose(Aig_Regular(temp1), 1);
                   //     cout << endl;
                }
                 else 
                 {
                     temp1 = createFuncT (p, newYCi, Ymap, graph, secVar, nodeOp); //Create it
                     funcT[secVar] = temp1;
                 }
             }

               if (rhs2 == NULL)
               {
                    rhs2 = Aig_NotCond(temp1, pos);
                 //   Aig_ObjPrintVerbose(Aig_Regular(rhs2), 1);
                    cout << endl;

                    continue;
               }

                    
                if (op == 1)
                    rhs2 = Aig_And (p, Aig_NotCond(temp1, pos), temp=rhs2);
                else
                {
                    if (op == 2)
                        rhs2 = Aig_Or (p, Aig_NotCond(temp1, pos), temp=rhs2);
                    else
                        rhs2 = Aig_Exor (p, Aig_NotCond(temp1, pos), temp=rhs2);
                }
            }

            //cout << "Adding " << endl;
            //Aig_ObjPrintVerbose(Aig_Regular(rhs2),  1);
            //cout << " To FuncT " << node << " And q2AigMap " << endl;
        //}
     //   funcT[var] = rhs2; //Should I do an Aig_Regular Here?
      //  qd2AigMap[var] = rhs2; //Why is this needed?
        return rhs2;
	}
*/


//Check Syntactic Independence 
//Return 0 means independent of X
//Return 1 means independent of Y
//Return -1 means not independent
//It is  inefficient - should be improved.
int checkSynInd (Aig_Man_t* pMan, vector <int>& indX, vector<int>& indY) 
{
    //if (pMan == NULL)
     //   cout << " In Syn Ind Check, Aig Manager NULL " << endl;

    //cout << " First getting support  - in Syn Ind check " << endl; 

    //printAig (pMan);
    vector <Aig_Obj_t*> supportVec = Aig_SupportVec(pMan, Aig_ManCo(pMan, 0));

    //cout << " Obtained support  - in Syn Ind check " << endl; 
    //cout << " Size " << supportVec.size() << endl;

    int i;
    bool ind = true;
    //cout << "Support " << endl;
    //for (i = 0; i < supportVec.size() ; i++)
    //{
	 //   Aig_ObjPrintVerbose( supportVec[i], 1 ), printf( "\n" );
    //}
    for (i = 0; i < numX ; i++)
    {
        
        if (find (supportVec.begin(), supportVec.end(), Aig_ManObj(pMan, varsXF[i])) != supportVec.end())
        {
            indX[i] = -1;
            ind = false;
        }
        else
            indX[i] = 1;

    }
    if (ind) return 0; //Syntactically independent of X

    ind = true;
    
    for (i = 0; i < numY ; i++)
    {
        if (find (supportVec.begin(), supportVec.end(), Aig_ManObj(pMan, varsYF[i])) != supportVec.end())
        {
            indY[i] = -1;
            ind = false;
        }
        else
            indY[i] = 1;
    }
    if (ind) return 1; //Syntactically independent of Y

    return -1;
    
}
//Function which checks for semantic independence of X and Y

//Return 0 means independent of X
//Return 1 means independent of Y
//Return -1 means not independent
//Copied from helper.cpp and modified appropriately
int checkSemInd (Aig_Man_t* FAig, vector <int>& indX, vector<int>& indY)
{

//	auto unate_start = std::chrono::steady_clock::now();
//	auto unate_end = std::chrono::steady_clock::now();
//	auto unate_run_time = std::chrono::duration_cast<std::chrono::microseconds>(unate_end - unate_start).count()/1000000.0;

	cout << " Preparing for semantic independence checks " << endl;
	sat_solver* pSat = sat_solver_new();
	Cnf_Dat_t* SCnf = Cnf_Derive(FAig, Aig_ManCoNum(FAig));
	addCnfToSolver(pSat, SCnf);
    //Cnf_DataPrint(SCnf, 1);
	int numCnfVars = SCnf->nVars;
	Cnf_Dat_t* SCnf_copy = Cnf_DataDup(SCnf);
 	Cnf_DataLift (SCnf_copy, numCnfVars);	
	addCnfToSolver(pSat, SCnf_copy);
	int status, numUnate, totalNumUnate = 0;
//	assert(unate.size()==numY);
//Equate the X's and Y's. 
 //	int x_iCnf, y_iCnf; 
	lit Lits[3];
	int cont_XVars[numX]; //control Variables
    int retVal = -1;
	for(int i = 0; i < numX; ++i) {
    //cout << "i = " << i << " indX " << indX[i] << endl;
        if (indX[i] == -1) //It is not syntactically independent
        //Equate the X'es of the two CNFs in the presence of control variables. If control variable c1 
        // is true, than the equality does not hold. If it is false, the variables are forced equal.
        {   
            cont_XVars[i] = sat_solver_addvar (pSat);   //
            Lits[0] = toLitCond( SCnf->pVarNums[ varsXF[i]], 0 );
            Lits[1] = toLitCond( SCnf_copy->pVarNums[ varsXF[i]], 1 );
            Lits[2] = Abc_Var2Lit (cont_XVars[i], 0);
        //	cout << i  << " : Adding clause " <<  Lits [0] << " " << Lits [1] << " " << Lits[2] << endl;
                if ( !sat_solver_addclause( pSat, Lits, Lits+3 ) )
                        assert( 0 );
            Lits[0] = toLitCond( SCnf->pVarNums[ varsXF[i]], 1 );
            Lits[1] = toLitCond( SCnf_copy->pVarNums[ varsXF[i]], 0 );
            Lits[2] = Abc_Var2Lit (cont_XVars[i], 0);
	   	 //   cout << i << " : Adding clause " <<  Lits [0] << "  " << Lits [1] << "  " << Lits[2] << endl;
                if ( !sat_solver_addclause( pSat, Lits, Lits+3 ) )
                        assert( 0 );
        }
	}

	int cont_YVars[numY]; //control Variables
	for(int i = 0; i < numY; ++i) {
    //cout << "i = " << i << " indY " << indY[i] << endl;
        if (indY[i] == -1) //It is present in the support. Add equality clauses for the Y variables
        {
            cont_YVars[i] = sat_solver_addvar (pSat);
            Lits[0] = toLitCond( SCnf->pVarNums[ varsYF[i]], 0 );
            Lits[1] = toLitCond( SCnf_copy->pVarNums[ varsYF[i]], 1 );
            Lits[2] = Abc_Var2Lit (cont_YVars[i], 0);
    	//	cout << " Adding clause for " << i << " "  <<  Lits [0] << " " << Lits [1] << " " << Lits [2] << endl;
                if ( !sat_solver_addclause( pSat, Lits, Lits+3 ) )
                        assert( 0 );
            Lits[0] = toLitCond( SCnf->pVarNums[ varsYF[i]], 1 );
            Lits[1] = toLitCond( SCnf_copy->pVarNums[ varsYF[i]], 0 );
            Lits[2] = Abc_Var2Lit (cont_YVars[i], 0);
    	//	cout << " Adding clause for " << i << " "  <<  Lits [0] << " " << Lits [1] << " " << Lits [2] << endl;
                if ( !sat_solver_addclause( pSat, Lits, Lits+3 ) )
                        assert( 0 );
         }
	}
	
    

	//cout << "NumCnfVars " <<  numCnfVars << endl;
	//cout << "SCnfVars " <<  SCnf->nVars << endl;
	int coID = getCnfCoVarNum(SCnf, FAig, 0);
	
	Aig_Obj_t * pCo = Aig_ManCo(FAig, 0);
	assert (coID == SCnf->pVarNums[pCo->Id]);

//Add the bi-implication \neg (F <=> F')
    lit biImp[2];
	biImp[0] = toLitCond( SCnf->pVarNums[pCo->Id],0);	
	biImp[1] = toLitCond(SCnf_copy->pVarNums[pCo->Id],0); 
    //cout << " Adding clause 1 for biImp " <<  biImp [0] << " " << biImp[1]  << endl;
    if ( !sat_solver_addclause( pSat, biImp, biImp+2 ) )
                  assert( 0 );
	biImp[0] = toLitCond( SCnf->pVarNums[pCo->Id],1);	
	biImp[1] = toLitCond(SCnf_copy->pVarNums[pCo->Id],1); 
    //cout << " Adding clause 2 for biImp " <<  biImp [0] << " " << biImp[1]  << endl;
    if ( !sat_solver_addclause( pSat, biImp, biImp+2 ) )
                  assert( 0 );


	lit LA[numX+ numY];
	int index;
    int asIndex = 0;
    int numIndX = 0;
   //Check for semantic independence for each X. Break if even one is not independent 
	for (int i = 0; i < numX; ++i)
	{
          if (indX[i] == 1) //already independent of X
          {
              numIndX ++;
              continue;
          }
          asIndex = 0;
                
		  for (int j = 0; j < numX; j++)
		  {
         //       cout << "j = " << j << " " << indX[j] << endl;
                if (indX[j] == -1)
                { 
                    if (j == i)
                    {
                  //      cout << " adding X : j =  " << j << " i = " << i << Abc_Var2Lit (cont_XVars[j], 0)  << " to assumptions " << endl;
                        LA[asIndex++] = Abc_Var2Lit (cont_XVars[j], 0); // 
                    }
                    else
                    {
                 //       cout << " adding X : j =  " << j << " i = " << i << Abc_Var2Lit (cont_XVars[j], 1)  << " to assumptions " << endl;
                        LA[asIndex++] = Abc_Var2Lit (cont_XVars[j], 1);
                    }
                } 
		  }

		  for (int j = 0; j < numY; j++)
		  {
                if (indY[j] == -1)
                {
				     LA[asIndex++] = Abc_Var2Lit (cont_YVars[j], 1);
            //            cout << " adding Y : j =  " << j << Abc_Var2Lit (cont_YVars[j], 1)  << " to assumptions " << endl;
                }
		  }

				// Check if semantically independent
			//LA[0] = toLitCond(SCnf->pVarNums[varsYF[i]], 1); //check the 0 and 1's
			//LA[1] = toLitCond(SCnf_copy->pVarNums[varsYF[i]], 0);
				//cout << "Printing assumptions for pos unate : " << LA [0] << " " << LA [1] << " " << LA [2] << " " << LA [3] << endl;
			status = sat_solver_solve(pSat, LA, LA+asIndex, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0);
           
				//cout << "Status of sat solver " << status << endl;
			if (status == l_False) {
				indX[i] = 1;
				cout << "Var x" << i << " (" << varsXF[i] << ") is semantically independent" << endl;
				addVarToSolver(pSat, cont_XVars[i], 1); //Should I add 0 or 1?? Do I need to add anything?
				numIndX++;
			}
            else
            {
                if (status == l_True)
                {
				    cout << "Var x" << i << " (" << varsXF[i] << ") is not semantically independent" << endl;
                    //break;

                }
            }
		}
        if (numIndX == numX)
        {
		    cout << "F semantically independent of X " << endl;
            retVal = 0;
        }

	//	unate_end = std::chrono::steady_clock::now();
	//	unate_run_time = std::chrono::duration_cast<std::chrono::microseconds>(unate_end - main_time_start).count()/1000000.0;
	//	if( unate_run_time >= options.unateTimeout) {
	//		cout << "checkUnateSemanticAll Timed Out. Timeout = " << options.unateTimeout << endl;
	//		break;
	//	}
    //Checking for semantic independence of Y
    if (retVal == -1)
    {
        int numIndY = 0;

        for (int i = 0; i < numY; ++i)
        {

              if (indY[i] == 1) //already independent of Y
              {
                  numIndY ++;
                  continue;
              }
                    
              asIndex = 0;
              for (int j = 0; j < numY; j++)
              {
                    if (indY[j] == -1)
                    {
                        if (j == i)
                            LA[asIndex++] = Abc_Var2Lit (cont_YVars[j], 0);
                        else
                            LA[asIndex++] = Abc_Var2Lit (cont_YVars[j], 1);
                        //cout << " adding Y : j =  " << j << " " << Abc_Var2Lit (cont_YVars[j], 1)  << " to assumptions " << endl;
                    }
              }
             // cout << " numX = " << numX  << " " << indX.size() << endl ;

              for (int j = 0; j < numX; j++)
              {
                    if (indX[j] == -1)
                    {
                        LA[asIndex++] = Abc_Var2Lit (cont_XVars[j], 1);
                        //cout << " adding X : j =  " << j << " i = " << i <<  " " << Abc_Var2Lit (cont_XVars[j], 1)  << " to assumptions " << endl;
                     }
              }

               // Sat_SolverWriteDimacs (pSat, "semcheck.qdimacs", LA, LA+asIndex, 0);
                status = sat_solver_solve(pSat, LA, LA+asIndex, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0);
                    //cout << "Status of sat solver " << status << endl;
                if (status == l_False) {
                    indY[i] = 1;
                    cout << "Var y" << i << " (" << varsYF[i] << ") is semantically independent" << endl;
                    addVarToSolver(pSat, cont_YVars[i], 1); //Should I add 0 or 1?? Do I need to add anything?
                    numIndY++;
                }
                else
                {
                    if (status == l_True)
                    {
                        cout << "Var y" << i << " (" << varsYF[i] << ") is not semantically independent" << endl;
                      //  break;

                    }
                }
            }

         if (numIndY == numY) {
            cout << "F semantically independent of Y " << endl;
                retVal =  1;
         }
     }
	sat_solver_delete(pSat);
	Cnf_DataFree(SCnf);
	Cnf_DataFree(SCnf_copy);
    indX.resize(0);
    indY.resize(0);

//	cout << "TotalNumUnate =  " << totalNumUnate << endl;
	return retVal; 

}
