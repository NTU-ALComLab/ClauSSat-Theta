#ifndef PROMPT_HH
#define PROMPT_HH
#include <memory>
#include "graph.hh"
#include "linObjFunc.hh"
using namespace std;

Model readPartialModel(int nbVars, const vector<string>& fields);
Graph parseFromNNF(const string& path);
WeightVector parseFromWeights(const string& path, int nbVars);
void parseMinimization(const std::shared_ptr<Graph> g, string path) ;
std::shared_ptr<Graph> parseMinimizationAndCond(const std::shared_ptr<Graph> g, string path);
void conditionGraph(std::shared_ptr<Graph> g, const vector<string>& fields);
void printModelCount(const shared_ptr<Graph>& g, const vector<string>& fields);

// Print available commands
void printHelp();

// Prompt starts an interactive session through the console.
// It returns when the users asks so.
void prompt();

#endif
