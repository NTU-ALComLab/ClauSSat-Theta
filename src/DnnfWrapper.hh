#ifndef DNNFWRAPPER_HH
#define DNNFWRAPPER_HH

#include <algorithm>
#include "prompt.hh"
#include "parser.hh"
#include "math.h"
#include "cassert"
using namespace std;

class DNNFCounter{
public:
    DNNFCounter (std::istream& in): dnnf_(parseNNF(in)){}
    DNNFCounter () {};

    void set_lit_weight(int lit, double weight){
        dnnf_.setLitWeight(lit, weight);
    }

    double assump_model_count(vector<int> assumps){
        Model partialModel{dnnf_.nbVars};
        for(int& lit : assumps)
            partialModel.setBindingFor(abs(lit), lit>0 ?  Binding::True : Binding::False );
        mpq_class mc = dnnf_.modelCount(partialModel);
        return mc.get_d();
    }

    void condition_on(vector<int> assertions){
        Model partialModel{dnnf_.nbVars};
        for(int& lit : assertions)
            partialModel.setBindingFor(abs(lit), lit>0 ?  Binding::True : Binding::False );
        dnnf_.conditionTo(partialModel);
    }

    int get_vars_num(){
        return dnnf_.nbVars;
    }

private:
    Graph           dnnf_;
};

#endif