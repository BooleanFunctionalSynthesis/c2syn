#ifndef _BASICS_H
#define _BASICS_H

#include <vector>
#include <cstdlib>
#include <iostream>

using namespace std;


#define FULL_DDNNF

class CSolverConf
{
public:
    static bool analyzeConflicts;
    static bool doNonChronBackTracking;

    static bool quietMode;

    static bool allowComponentCaching;
    static bool allowImplicitBCP;

    static bool allowPreProcessing;

    static unsigned int secsTimeBound;

    static unsigned int maxCacheSize;   // maximum Cache Size in bytes
    
    static int nodeCount; // Nodes currently in use
    
    static bool smoothNNF;
    static bool ensureAllLits;
    
    static bool disableDynamicDecomp;

    CSolverConf();

    ~CSolverConf();

};

#ifdef COMPILE_FOR_GUI
#define toSTDOUT(X)
#else
#define toSTDOUT(X)	if(!CSolverConf::quietMode) cout << X;
#endif


#ifdef COMPILE_FOR_GUI
#define toERROUT(X)
#else
#define toERROUT(X)	if(!CSolverConf::quietMode) cout << X;
#endif

#ifdef DEBUG
#define toDEBUGOUT(X) if(!CSolverConf::quietMode) cout << X;
#else
#define toDEBUGOUT(X)
#endif


enum SOLVER_StateT
{

    SUCCESS,
    TIMEOUT,
    ABORTED
};

enum TriValue //Expanding the TriValue to include inputs and Tseitin
{

    F = 0,
    W = 1,
    X = 2
  //  I = 3,
   // T = 4
};

enum DT_NodeType
{
    DT_AND,
    DT_OR,
    DT_LIT,
    DT_TOP,
    DT_BOTTOM
};


extern char TriValuetoChar(TriValue v);
#endif
