#include "helper.h"
enum nodetype {VAR, AND, OR, COMP};

class Node: public
{
    int id;
    static int numNodes; //to assign an id to each node;
    nodetype type; // 0:
    int varId; //if node type is lit (then varId)
    Node* left;
    Node* right;
    vector<int> clauses;
    vector<int> consts;

    Node::Node ()
    {
        id = numNodes ++;
    }
}; 


Node * root;
vector<Node> allNodes;





