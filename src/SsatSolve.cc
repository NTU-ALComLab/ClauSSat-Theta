#include <signal.h>
#include <cassert>
#include <numeric>
#include <string>
#include "QestoGroups.hh"
#include "ClausesInversion.hh"
#include "LitBitSet.hh"
#include "unistd.h"

using SATSPC::Lit;
using SATSPC::lit_Undef;
using SATSPC::vec;

#define WCNF_FILE "wmc/temp.wcnf"
#define NNF_FILE  "wmc/temp.nnf"
#define CNF_FILE  "wmc/temp.cnf"
#define LOG_FILE "wmc/temp.log"
#define SATPROB_FILE "wmc/satProb.log"
#define LEVEL_CNF "wmc/level.cnf"
#define LEVEL_NNF "wmc/level.nnf"
#define dDNNF_COMPILER "bin/d4"

// using namespace std;

/* Helper functions */
bool check_and_encode(vec<bool> &encoded, Var v);
Var mapVar(Var v, vec<Var> &map, Var &max);
Var mapVar(Var v, vector<Var>& map, Var& max);
void concat_assumptions(vec<Lit> &concat, vec<Lit> &assump1, vec<Lit> &assump2);
void print_encgrps(const vector<EncGrp> &enc_groups);
bool is_file_empty(ifstream& f);

double QestoGroups::solve_ssat(bool alreadyUnsat)
{
#ifndef NDEBUG
    for (size_t i = 0; i < levs.lev_count(); ++i)
    {
        cout << "LEV " << i << ": ";
        for (size_t gi : groups.groups(i))
            cout << gi << ' ';
        cout << endl;
    }
#endif
    if (alreadyUnsat)
    {
        cout << "Contains an empty clause in cnf." << endl;
        return 0;
    }
    return solve_ssat_recur(0);
}

double QestoGroups::solve_ssat_recur(size_t qlev)
{
    if (profiler.is_timeout())
    {
        output_ssat_sol(false);
        cout << profiler << endl;
        exit(0);
    }

    abstractions[qlev].simplify();

    double ret = 0, prob = 0;
    bool sat = true;
    vec<Lit> parent_selection;
    vec<Lit> assump;
    vec<Lit> concat;
    vector<EncGrp> enc_max_lev_selection;
    vector<EncGrp> enc_groups;

    // Get selection from previous level
    get_parent_selection(qlev, parent_selection);
    parent_selection.copyTo(assump);

    if (opt.get_cache() && lookup(qlev, parent_selection, ret))
    {
        ret_prob[qlev] = ret;
        return ret;
    }
    ret_prob[qlev] = 0;

    bool has_thres = levs.has_threshold(qlev);
    double thres_prob = levs.get_thres(qlev);

    // Last level
    if (qlev == levs.lev_count() - 1)
    {
        sat = solve_selection(qlev, parent_selection);
        sat ? ++profiler.selSATCnts[qlev] : ++profiler.selUNSATCnts[qlev];
        if (levs.level_type(qlev) == EXISTENTIAL)
        {
            if (sat)
                minimal_selection_e(qlev, 1, parent_selection);
            if (!sat)
                mini_unsat_core(qlev);
            ret = sat;
        }
        else
        { // RANDOM
            if (sat)
            {
                vector<vector<EncGrp>> enc_sel_lits;
                for (size_t gi : groups.groups(qlev))
                    if (qlev == 0 || groups.is_select(groups.parent(gi)))
                        enc_sel_lits.push_back(vector<EncGrp>({encode_sel(gi, 0)}));
                if (opt.get_increMC())
                    ret = assump_level_wmc(qlev, enc_sel_lits);
                else
                    ret = selection_WMC(qlev, enc_sel_lits);
            }
            else
            {
                mini_unsat_core(qlev);
                ret = 0;
            }
        }
        if (has_thres) // map prob -> 1/0
            ret = ret >= thres_prob;
        if (opt.get_cache())
            record(qlev, parent_selection, ret);
        ret_prob[qlev] = ret;
        return ret;
    }
    assert(qlev != levs.lev_count() - 1);

    while (sat)
    {
        assert(qlev < levs.lev_count());

// Solve selection TODO: add assump!!!
#ifndef NDEBUG
        cout << "Solve selection @ ";
#endif
        sat = solve_selection(qlev, assump);
        sat ? ++profiler.selSATCnts[qlev] : ++profiler.selUNSATCnts[qlev];

        if (levs.level_type(qlev) == EXISTENTIAL)
        {
            if (sat)
            {
                // TODO: Minimal clause selection
                bool alreadySat = minimal_selection_e(qlev, 0, parent_selection);
                prob = alreadySat ? 1 : solve_ssat_recur(qlev + 1);
#ifndef NDEBUG
                cout << getSolverName(qlev) << " solve prob = " << prob << '\n';
#endif

                if (prob > ret)
                {
                    ret = ret_prob[qlev] = prob;
                    // Update level selection with max prob
                    enc_max_lev_selection.clear();
                    for (size_t gi : groups.groups(qlev))
                        enc_max_lev_selection.push_back(encode_sel(gi, groups.is_lev_select(gi)));

#ifndef NDEBUG
                    cout << getSolverName(qlev) << " update max prob = " << ret << '\n';
                    print_encgrps(enc_max_lev_selection);
                    cout << '\n';
#endif
                    if (qlev == 0)
                        cout << "Update solution, value = " << ret << "\t(time = " << profiler.get_tot_time() << ")\n";
                }

                if (prob == 1 || (has_thres && prob >= thres_prob))
                { // early termination
                    minimal_selection_e(qlev, 1, parent_selection);
                    break;
                }

                // Add learnt clause
                get_learnt_clause_e(qlev, enc_groups, prob == 0);
                if (opt.get_partial())
                    partial_assignment_pruning(qlev, enc_groups, ret);
                add_learnt_clause_e(qlev, enc_groups, assump, prob == 0);
                if (prob == 0)
                    push_unsat_core(qlev, enc_groups, assump);
            }
            else
            {
                // Restore level selection with max prob
                for (EncGrp enc_gi : enc_max_lev_selection)
                    groups.set_lev_select(get_group(enc_gi), get_select(enc_gi));
                minimal_selection_e(qlev, 1, parent_selection);
                break;
            }
        }
        else if (levs.level_type(qlev) == RANDOM)
        {
            if (sat)
            {
                prob = solve_ssat_recur(qlev + 1);
                /* minimal_selection_r(qlev, selection); */
                // prune selection
                get_learnt_clause_r(qlev, enc_groups, prob == 0);
#ifndef NDEBUG
                cout << "Orig learnt: ";
                print_encgrps(enc_groups);
                cout << '\n';
#endif
                if (prob == 1)
                    remove_lits(enc_groups, 0);
                if (prob == 0)
                    remove_lits(enc_groups, 1);
#ifndef NDEBUG
                if (prob == 0 || prob == 1)
                {
                    cout << "Lits remove: ";
                    print_encgrps(enc_groups);
                    cout << '\n';
                }
#endif
                // maximal pruning
                if (opt.get_partial())
                    partial_assignment_pruning(qlev, enc_groups, prob);
                // Record mapping from 'prob' to 'learnt clause'
                if(prob!=0)
                    prob2Learnts[qlev][prob].push_back(enc_groups);
#ifndef NDEBUG
                cout << getSolverName(qlev) << " store " << prob << " -> ";
                print_encgrps(enc_groups);
                cout << '\n';
#endif

                add_learnt_clause_r(qlev, enc_groups, assump, prob == 0);
                if (prob == 0)
                    push_unsat_core(qlev, enc_groups, assump);
            }
            else
            {
                // TODO incremental

                if(!prob2Learnts[qlev].empty()){
                    if(opt.get_increMC()){
                        ret = incre_calculate_prob(qlev, prob2Learnts[qlev], has_thres, thres_prob);
                        // double ref = calculate_prob(qlev, prob2Learnts[qlev]).first;
                        // cout << "ref / imp = " << ref << " / " << ret << endl;
                        // cout << "qlev = " << qlev << endl;
                        // if(ref != ret){
                            // cout << "Warning!! Error Probability" << endl;
                            // exit(1);
                        // }
                    }
                    else{
                        ret = calculate_prob(qlev, prob2Learnts[qlev]).first;
                    }
                    prob2Learnts[qlev].clear();
                }
                break;
            }
        }
    }

    for (int i = parent_selection.size(); i < assump.size(); ++i)
        abstractions[qlev].addClause(~assump[i]);

    if (has_thres)
        ret = ret >= thres_prob;

    if (opt.get_cache() && ret != -1)
        record(qlev, parent_selection, ret);
    ret_prob[qlev] = ret;
    if (ret == -1)
        ++profiler.partialWMC;

    return ret;
}

bool QestoGroups::solve_selection(size_t qlev, const vec<Lit> &assump)
{
    profiler.set_SAT_time();
    bool sat = abstractions[qlev].solve(assump);
    profiler.accum_SAT_time();
#ifndef NDEBUG
    cout << getSolverName(qlev) << ": " << (sat ? "" : "UNSAT") << '\n';
#endif
    if (sat)
    {
#ifndef NDEBUG
        size_t nSelected = 0, nLevSelected = 0;
#endif
        for (size_t gi : groups.groups(qlev))
        {
            groups.set_select(gi, svalue(gi));
            groups.set_lev_select(gi, tvalue(gi));
#ifndef NDEBUG
            if (svalue(gi))
                ++nSelected;
            if (groups.is_select(groups.parent(gi)) && tvalue(gi))
                ++nLevSelected;
#endif
        }
#ifndef NDEBUG
        cout << "S: ";
        for (size_t gi : groups.groups(qlev))
            if (qlev == 0 || groups.is_select(groups.parent(gi)))
                cout << gi << (svalue(gi) ? "" : "\'") << ' ';
        cout << endl;
        cout << "T: ";
        for (size_t gi : groups.groups(qlev))
            if (qlev == 0 || groups.is_select(groups.parent(gi)))
                cout << gi << (tvalue(gi) ? "" : "\'") << ' ';
        cout << endl;
        cout << "#     selected grps : " << nSelected << '\n';
        cout << "# Lev selected grps : " << nLevSelected << '\n';
#endif
    }
    return sat;
}

void QestoGroups::get_parent_selection(size_t qlev, vec<Lit> &parSel)
{
    parSel.clear();
    if (qlev > 0)
        for (size_t gi : groups.groups(qlev - 1))
            parSel.push(groups.is_select(gi) ? mkLit(p(qlev, gi)) : ~mkLit(p(qlev, gi)));
}

void QestoGroups::get_learnt_clause_e(size_t qlev, vector<EncGrp> &enc_groups, bool isZero)
{
    assert(qlev < levs.lev_count() - 1);
    assert(levs.level_type(qlev) == EXISTENTIAL);

    enc_groups.clear();
    for (size_t gi : groups.groups(qlev))
        if (groups.is_select(gi))
            enc_groups.push_back(encode_sel(gi, 0));
    /* if (qlev == levs.lev_count() - 2 && isZero) { */
    /*     for (size_t gc : groups.groups(qlev + 1)) { */
    /*         if (groups.is_lev_select(gc)) */
    /*             enc_groups.push_back( encode_sel(groups.parent(gc), 0) ); */
    /*     } */
    /* } */
    /* else { */
    /*     for (size_t gi : groups.groups(qlev)) */
    /*         if (groups.is_select(gi)) enc_groups.push_back( encode_sel(gi, 0) ); */
    /* } */

    /* eLearnt.clear(); */
    /* if (opt.get_partial()) { */
    /*     for (size_t gi : groups.groups(qlev)) { */
    /*         if (!groups.is_select(gi)) continue; */
    /*         if (opt.get_pin()) { */
    /*             const vector<Pin*>& ps = groups.getPins(gi); */
    /*             for (Pin * pP : ps) eLearnt.push( mkLit(pinVar(qlev, pP->id)) ); */
    /*         } */
    /*         else { */
    /*             const LitSet& ls = groups.lits(gi); */
    /*             FOR_EACH(li, ls) eLearnt.push( *li ); */
    /*         } */
    /*     } */
    /*     remove_duplicate_lits( qlev, eLearnt ); */
    /* } */
    /* else { */
    /*     for (size_t gi : groups.groups(qlev)) */
    /*         eLearnt.push( ~mkLit(s(qlev,gi)) ); */
    /* } */
}

void QestoGroups::add_learnt_clause_e(size_t qlev, vector<EncGrp> &enc_groups, vec<Lit> &assump, bool always_enable)
{
    assert(qlev < levs.lev_count() - 1);
    assert(levs.level_type(qlev) == EXISTENTIAL);

    vec<Lit> learnt_clause;
    learnt_clause.capacity(enc_groups.size() + 1);
    for (EncGrp enc_gi : enc_groups)
    {
        assert(!get_select(enc_gi));
        learnt_clause.push(~mkLit(s(qlev, get_group(enc_gi))));
    }

    if (!always_enable)
    {
        Var v = abstractions[qlev].newVar();
        learnt_clause.push(mkLit(v));
        assump.push(~mkLit(v));
    }
    abstractions[qlev].addClause(learnt_clause);

#ifndef NDEBUG
    cout << getSolverName(qlev) << " learns ";
    print_encgrps(enc_groups);
    cout << '\n';
#endif
    profiler.learntClaLen += enc_groups.size();
    profiler.learntClaNum += 1;
}

void QestoGroups::get_learnt_clause_r(size_t qlev, vector<EncGrp> &enc_groups, bool isZero)
{
    assert(levs.level_type(qlev) == RANDOM);
    assert(qlev < levs.lev_count()-1);

    ++profiler.pruneCnt;
    enc_groups.clear();
    EncGrp enc_gi;
    size_t numSelected = 0;

    for (size_t gi : groups.groups(qlev))
    {
        if (qlev && !groups.is_select(groups.parent(gi)))
            continue;
        ++numSelected;

        enc_gi = encode_sel(gi, !groups.is_lev_select(gi));
        if (levs.level_type(qlev+1)==RANDOM){ // next level is RANDOM with threshold
            enc_groups.push_back(enc_gi);
        }
        else{
            if (groups.is_lev_select(gi))
            {
                enc_groups.push_back(enc_gi);
                continue;
            }
            const vector<size_t> &children = groups.get_children(gi);
            for (size_t gc : children)
            {
                if (groups.is_lev_select(gc))
                {
                    enc_groups.push_back(enc_gi);
                    break;
                }
            }
        }
    }
    /* for (size_t gc : groups.groups(qlev + 1)) { */
    /*     if (qlev == 0 || groups.is_select(groups.grandparent(gc))) { */
    /*         size_t gp = groups.parent(gc); */
    /*         /1* if (enc_groups.size() && gp == get_group( enc_groups.back() )) continue; *1/ */
    /*         if (groups.is_lev_select(gp) || groups.is_lev_select(gc)) { */
    /*             /1* if (qlev == levs.lev_count() - 2 && isZero && *1/ */
    /*             /1*     !(groups.is_lev_select(gp) && groups.is_lev_select(gc))) continue; *1/ */
    /*             enc_gi = encode_sel(gp, !groups.is_lev_select(gp)); */
    /*             if (enc_groups.empty() || enc_gi != enc_groups.back()) */
    /*                 enc_groups.push_back(enc_gi); */
    /*         } */
    /*     } */
    /* } */

    assert(numSelected >= enc_groups.size());
    profiler.pruneClaCnt += numSelected - enc_groups.size();
}

void QestoGroups::add_learnt_clause_r(size_t qlev, vector<size_t> &enc_groups, vec<Lit> &assump, bool always_enable)
{
    assert(qlev < levs.lev_count() - 1);
    assert(levs.level_type(qlev) == RANDOM);

    vec<Lit> learnt_clause;
    learnt_clause.capacity(enc_groups.size() + 1);
    size_t gi;
    for (EncGrp enc_gi : enc_groups)
    {
        gi = get_group(enc_gi);
        learnt_clause.push(get_select(enc_gi) ? mkLit(s(qlev, gi)) : ~mkLit(s(qlev, gi)));
    }
    if (!always_enable)
    {
        Var v = abstractions[qlev].newVar();
        learnt_clause.push(mkLit(v));
        assump.push(~mkLit(v));
    }
    abstractions[qlev].addClause(learnt_clause);

#ifndef NDEBUG
    cout << getSolverName(qlev) << " learns ";
    print_encgrps(enc_groups);
    cout << '\n';
#endif
    profiler.learntClaLen += enc_groups.size();
    profiler.learntClaNum += 1;
}

/* If current level cannot deselect at least one clause of the unsat core,
 * the previous level should deselect one of their parents */
void QestoGroups::push_unsat_core(size_t qlev, vector<EncGrp> &enc_groups, vec<Lit> &tmpLits)
{
    if (qlev == 0)
        return;
    if (levs.level_type(qlev) == EXISTENTIAL)
        return;

    ++profiler.pushUNSATCoreAttempt;

    /* vec<Lit> assump; */
    /* assump.capacity(tmpLits.size()); */
    /* int n = groups.groups(qlev-1).size(); */
    /* for (int i = 0; i < n; ++i) */
    /*     assump.push(tmpLits[i]); */
    /* for (int i = n; i < tmpLits.size(); ++i) */
    /*     assump.push(~tmpLits[i]); */

    bool all_empty = true;
    for (EncGrp enc_gi : enc_groups)
    {
        size_t gi = get_group(enc_gi);
        if (groups.lits(gi).size())
        {
            all_empty = false;
            break;
        }
    }
    /* if (!abstractions[qlev].solve(assump)) { */
    if (all_empty)
    {
        if (levs.level_type(qlev) == RANDOM)
        {
            for (size_t gp : groups.groups(qlev - 1))
                groups.set_select(gp, 0);
            for (EncGrp enc_gi : enc_groups)
            {
                size_t gp = groups.parent(get_group(enc_gi));
                groups.set_select(gp, 1);
            }
        }
        else
        {
            assert(ret_prob[qlev] == 0);
            for (size_t gp : groups.groups(qlev - 1))
            {
                groups.set_select(gp, 0);
                groups.set_lev_select(gp, 0);
            }
            for (EncGrp enc_gi : enc_groups)
            {
                size_t gp = groups.parent(get_group(enc_gi));
                groups.set_select(gp, 1);
                groups.set_lev_select(gp, 1);
            }
        }
#ifndef NDEBUG
        cout << getSolverName(qlev) << " push unsat core!\n";
#endif
        ++profiler.pushUNSATCoreSuccess;
    }
}

void QestoGroups::partial_assignment_pruning(size_t qlev, vector<EncGrp> &enc_groups, double cur_prob)
{
#ifndef NDEBUG
    cout << "--- " << getSolverName(qlev) << " Enter partial" << endl;
    print_encgrps(enc_groups);
    cout << '\n';
#endif
    if (enc_groups.empty())
        return;

    size_t gi;
    double prob;
    vec<Lit> assump;
    /* vec<size_t> numLits; */
    bool isR = levs.level_type(qlev) == RANDOM;
    int dropIndex = enc_groups.size() - 1;
    int minIndex = isR ? sort_clause(qlev, enc_groups) : 0;
    if (minIndex == (int)enc_groups.size())
        return;

    if (opt.get_dynamic() && profiler.dropAttempts[qlev] >= 500)
    {
        profiler.dynamicAvgDones[qlev] = true;
        dropIndex -= profiler.dropCnts[qlev] / profiler.dropAttempts[qlev];
        if (dropIndex < minIndex)
            dropIndex = minIndex;
    }
    for (int i = enc_groups.size() - 1; i >= dropIndex; --i)
    {
        gi = get_group(enc_groups[i]);
        assert(groups.is_select(gi));
        groups.set_select(gi, !groups.is_select(gi));
        /* if (isR) { */
        /*     size_t add = 0; */
        /*     for (size_t gc : groups.get_children(gi)) { */
        /*         assump.push( mkLit( t(qlev+1, gc) ) ); ++add; */
        /*     } numLits.push(add); */
        /* } */
    }

    prob = solve_ssat_recur(qlev + 1);
    assert(!isR || prob >= cur_prob);
    if ((isR && prob == cur_prob) ||
        (!isR && prob <= cur_prob))
    {
        while (dropIndex > minIndex)
        {
            --dropIndex;
            gi = get_group(enc_groups[dropIndex]);
            assert(groups.is_select(gi));
            groups.set_select(gi, !groups.is_select(gi));
            /* if (isR) { */
            /*     size_t add = 0; */
            /*     for (size_t gc : groups.get_children(gi)) { */
            /*         assump.push( mkLit( t(qlev+1, gc) ) ); ++add; */
            /*     } numLits.push(add); */
            /* } */
            if (isR)
            { // check if selection is possible
                assump.clear();
                for (int i = 0; i <= dropIndex; ++i)
                {
                    size_t g = get_group(enc_groups[i]);
                    assump.push(mkLit(s(qlev, g), !groups.is_select(g)));
                }
                if (!abstractions[qlev].solve(assump))
                    continue;
            }

            prob = solve_ssat_recur(qlev + 1);
            assert(!isR || prob >= cur_prob);
            if ((isR && prob != cur_prob) ||
                (!isR && prob > cur_prob))
            {
                groups.set_select(gi, !groups.is_select(gi));
                /* if (isR) { */
                /*     int shrinkNum = numLits[enc_groups.size() - dropIndex - 1]; */
                /*     assert(assump.size() >= shrinkNum); */
                /*     assump.shrink(shrinkNum); */
                /* } */
                ++dropIndex;
                break;
            }
        }
    }
    else
    {
        if (opt.get_dynamic() && profiler.dynamicAvgDones[qlev])
        {
            while (dropIndex < (int)enc_groups.size())
            {
                gi = get_group(enc_groups[dropIndex]);
                groups.set_select(gi, !groups.is_select(gi));
                /* if (isR) { */
                /*     int shrinkNum = numLits[enc_groups.size() - dropIndex - 1]; */
                /*     assert(assump.size() >= shrinkNum); */
                /*     assump.shrink(shrinkNum); */
                /* } */
                ++dropIndex;
                prob = solve_ssat_recur(qlev + 1);
                assert(!isR || prob >= cur_prob);
                if ((isR && prob == cur_prob) ||
                    (!isR && prob <= cur_prob))
                    break;
            }
        }
        else
        {
            gi = get_group(enc_groups[dropIndex]);
            groups.set_select(gi, !groups.is_select(gi));
            ++dropIndex;
        }
    }

    assert(dropIndex >= 0 && dropIndex <= (int)enc_groups.size());
    profiler.dropCnts[qlev] += enc_groups.size() - dropIndex;
    ++profiler.dropAttempts[qlev];

#ifndef NDEBUG
    bool success = dropIndex != (int)enc_groups.size();
    if (success)
    {
        cout << getSolverName(qlev) << " Orig learnt: ";
        print_encgrps(enc_groups);
        cout << '\n';
    }
#endif

    enc_groups.resize(dropIndex);

#ifndef NDEBUG
    if (success)
    {
        cout << getSolverName(qlev) << " Trun learnt: ";
        print_encgrps(enc_groups);
        cout << '\n';
    }
    if (!success)
        cout << "Partial fail...\n";

    cout << "--- " << getSolverName(qlev) << " Exit partial" << endl;
#endif
}

int QestoGroups::sort_clause(size_t qlev, vector<EncGrp> &enc_groups) const
{
    int i, j;
    for (i = enc_groups.size(), j = i - 1; j >= 0; --j)
    {
        size_t gi = get_group(enc_groups[j]);
        if (!groups.is_select(gi))
            continue;
        bool isCandidate = true;
        for (size_t gc : groups.get_children(gi))
        {
            if (groups.is_lev_select(gc))
            {
                isCandidate = false;
                break;
            }
        }
        if (isCandidate)
        {
            --i;
            EncGrp tmp = enc_groups[i];
            enc_groups[i] = enc_groups[j];
            enc_groups[j] = tmp;
        }
    }
    return i;
}

void QestoGroups::remove_lits(vector<EncGrp> &enc_groups, bool selected)
{
    size_t i = 0;
    while (i < enc_groups.size())
    {
        if (get_select(enc_groups[i]) == selected)
        {
            enc_groups[i] = enc_groups.back();
            enc_groups.pop_back();
        }
        else
            ++i;
    }
}

// param = 0: same as er-ssat
// param = 1: try to deselect clauses at level qlev that are deselected at previous random level
bool QestoGroups::minimal_selection_e(size_t qlev, size_t param, vec<Lit> &parent_selection)
{
#ifndef NDEBUG
    cout << "--- Enter MSC" << param + 1 << endl;
#endif
    assert(levs.level_type(qlev) == EXISTENTIAL);

    bool sat = false, success = false;
    vec<Lit> block;
    vec<Lit> assump;
    parent_selection.copyTo(assump);

    while (true)
    {
        block.clear();
        assump.shrink(assump.size() - parent_selection.size());
        for (size_t gi : groups.groups(qlev))
        {
            if (param == 0)
            {
                if (groups.is_select(gi))
                    block.push(~mkLit(t(qlev, gi)));
                else if (qlev == 0 || groups.is_select(groups.parent(gi)))
                    assump.push(~mkLit(t(qlev, gi)));
            }
            else if (param == 1 && (qlev == 1 || groups.is_select(groups.grandparent(gi))))
            { // && !groups.is_select(groups.parent(gi))) ) {
                if (groups.is_lev_select(groups.parent(gi)))
                    assump.push(groups.is_lev_select(gi) ? mkLit(t(qlev, gi)) : ~mkLit(t(qlev, gi)));
                else
                    (groups.is_lev_select(gi)) ? block.push(~mkLit(t(qlev, gi))) : assump.push(~mkLit(t(qlev, gi)));
            }
        }
#ifndef NDEBUG
        cout << "    block: ";
        for (int i = 0; i < block.size(); ++i)
            cout << block[i] << ' ';
        cout << endl;
        cout << "    assump: ";
        for (int i = 0; i < assump.size(); ++i)
            cout << assump[i] << ' ';
        cout << endl;
#endif
        if (block.size() == 0)
        {
            success = true;
#ifndef NDEBUG
            cout << "All deselected!\n";
#endif
            break;
        }

        Var v = abstractions[qlev].newVar();
        block.push(mkLit(v));
        assump.push(~mkLit(v));

        abstractions[qlev].addClause(block);
        sat = solve_selection(qlev, assump);
        abstractions[qlev].addClause(mkLit(v)); // disable 'block'
        if (!sat)
            break;
        success = true;
    }
    if (success)
        param == 0 ? ++profiler.MCS1SuccCnt : ++profiler.MCS2SuccCnt;
    else
        param == 0 ? ++profiler.MCS1FailCnt : ++profiler.MCS2FailCnt;

#ifndef NDEBUG
    cout << (success ? "Success!\n" : "Failed\n");
    cout << "--- Exit MSC" << param + 1 << endl;
#endif
    return sat;
}

void QestoGroups::mini_unsat_core(size_t qlev)
{
    assert(qlev == levs.lev_count() - 1);
    if (levs.lev_count() == 1)
        return;

    vec<Lit> conflict;
    abstractions[qlev].conflict.copyTo(conflict);
    vec<bool> drop(conflict.size(), false);
    vec<Lit> assump;
    assump.capacity(conflict.size());
    vec<Lit> cla;

    for (int i = 0; i < conflict.size(); ++i)
    {
        assump.clear();
        for (int j = 0; j < drop.size(); ++j)
            if (i != j && !drop[j])
                assump.push(~conflict[j]);
        profiler.set_SAT_time();
        if (!abstractions[qlev].solve(assump))
            drop[i] = true;
        else
            cla.push(conflict[i]);
        profiler.accum_SAT_time();
    }

    if (levs.level_type(qlev) == RANDOM)
    {
        for (size_t gp : groups.groups(qlev - 1))
            groups.set_select(gp, false);
        for (int i = 0; i < cla.size(); ++i)
        {
            if (sign(cla[i]))
                groups.set_select(pv2gr[var(cla[i])], true);
        }
    }
    else
    {
        for (size_t gp : groups.groups(qlev - 1))
        {
            groups.set_select(gp, 0);
            groups.set_lev_select(gp, 0);
        }
        for (int i = 0; i < cla.size(); ++i)
        {
            if (sign(cla[i]))
            {
                groups.set_select(pv2gr[var(cla[i])], 1);
                groups.set_lev_select(pv2gr[var(cla[i])], 1);
            }
        }
    }

#ifndef NDEBUG
    cout << "MiniUnsatCore = ( ";
    for (int i = 0; i < cla.size(); ++i)
        cout << pv2gr[var(cla[i])] << (sign(cla[i]) ? "\'" : "") << ' ';
    cout << ")\n";
#endif
}

std::pair<double, double> QestoGroups::calculate_prob(size_t qlev, const ProbMap &prob2Learnt, bool countZero)
{

    // if (qlev == 0)
    //     cout << "Final count, # of WMC = " << prob2Learnt.size() << endl;
    double accum = 0, sel_prob, left = 1;
    for (auto it : prob2Learnt)
    {
        assert(accum >= 0 && it.first >= 0 && left >= 0);
        if (!countZero && it.first == 0)
            continue;
        if (accum + it.first * left < get_ret_prob((int)qlev - 1))
            return std::make_pair(-1, -1);

        sel_prob = 1 - selection_WMC(qlev, it.second);
        accum += it.first * sel_prob;
        left -= sel_prob;

        if (qlev == 0)
            cout << it.first << ": # of cubes = " << it.second.size() << ", prob = " << sel_prob << endl;
#ifndef NDEBUG
        cout << it.first << " x " << sel_prob << " + ";
#endif
    }
#ifndef NDEBUG
    cout << " = " << accum << endl;
    for (auto it : prob2Learnt)
    {
        cout << it.first << "\t: ";
        for (vector<EncGrp> &clause : it.second)
        {
            print_encgrps(clause);
            cout << '\n';
        }
        cout << '\n';
    }
#endif
    return std::make_pair(accum, accum + left);
}

double QestoGroups::selection_WMC(size_t qlev, const vector<vector<EncGrp>> &enc_learnts)
{
    ++profiler.WMCCnt;

    profiler.set_WMCIO_time();
    FILE *f = fopen(WCNF_FILE, "w");
    int length = 1024;
    char prob_str[length], cmd[length];

    to_dimacs_weighted(f, qlev, enc_learnts);
    profiler.accum_WMCIO_time();

    profiler.set_WMC_time();
    sprintf(cmd, "bin/cachet %s > %s", WCNF_FILE, LOG_FILE);
    if (system(cmd))
    {
        fprintf(stderr, "ERROR! Problems with cachet execution...\n");
        raise(SIGINT);
    }
    profiler.accum_WMC_time();

    profiler.set_WMCIO_time();
    sprintf(cmd, "grep \"Satisfying\" %s | awk '{print $3}' > %s", LOG_FILE, SATPROB_FILE);
    if (system(cmd))
    {
        fprintf(stderr, "ERROR! Problems with extracting probability to \"%s\"...\n", SATPROB_FILE);
        raise(SIGINT);
    }

    f = fopen(SATPROB_FILE, "r");
    if (!fgets(prob_str, length, f))
    {
        fprintf(stderr, "ERROR! Problems with reading probability from \"%s\"...\n", SATPROB_FILE);
        raise(SIGINT);
    }
    fclose(f);
    profiler.accum_WMCIO_time();
    return atof(prob_str);
}

void QestoGroups::to_dimacs_weighted(FILE *f, size_t qlev, const vector<vector<EncGrp>> &enc_learnts)
{
    size_t cnt = 0, gi;
    Var max = 1;
    vec<Var> map;
    vec<bool> encoded_group;
    bool selected;

    for (const vector<EncGrp> &enc_groups : enc_learnts)
    {
        if (enc_groups.empty())
        {
            fprintf(f, "p cnf 1 2\n1 0\n-1 0\n");
            fclose(f);
            return;
        }
        cnt += 1;
        for (EncGrp enc_gi : enc_groups)
        {
            gi = get_group(enc_gi);

            if (!check_and_encode(encoded_group, gi))
            {
                const LitSet &ls = groups.lits(gi);
                cnt += ls.size() + 1;
                // Map vars to 0 ~ max
                FOR_EACH(li, ls)
                mapVar(var(*li), map, max);
                mapVar(t(qlev, gi), map, max);
            }
        }
    }

    fprintf(f, "p cnf %d %ld\n", max - 1, cnt);

    for (int gi = 0; gi < encoded_group.size(); ++gi)
    {
        if (encoded_group[gi])
        {
            const LitSet &ls = groups.lits(gi);
            Var tvar = t(qlev, gi);
            FOR_EACH(li, ls)
            fprintf(f, "-%d %s%d 0\n", map[tvar], sign(*li) ? "" : "-", map[var(*li)]);
            FOR_EACH(li, ls)
            fprintf(f, "%s%d ", sign(*li) ? "-" : "", map[var(*li)]);
            fprintf(f, "%d 0\n", map[tvar]);
        }
    }

    for (const vector<EncGrp> &enc_groups : enc_learnts)
    {
        for (EncGrp enc_gi : enc_groups)
        {
            gi = get_group(enc_gi);
            selected = get_select(enc_gi);
            Var tvar = t(qlev, gi);
            fprintf(f, "%s%d ", selected ? "" : "-", map[tvar]);
        }
        fprintf(f, "0\n");
    }

    const vector<double> &probs = levs.get_probs();
    for (size_t i = 0, n = map.size(); i < n; ++i)
    {
        if (map[i] == -1)
            continue;
        assert(i >= probs.size() || probs[i] != -1);
        fprintf(f, "w %d %f\n", map[i], i < probs.size() ? probs[i] : -1);
    }

    fclose(f);
}

bool QestoGroups::lookup(size_t qlev, const vec<Lit> &parent_selection, double &prob)
{
    ++profiler.cacheLookup;
    CacheEntry entry(parent_selection);
    auto it = sel_caches[qlev].find(entry);
    if (it != sel_caches[qlev].end())
    {
        prob = (*it).prob;
        if (levs.level_type(qlev) == EXISTENTIAL)
        {
            const vector<bool> &sel = (*it).sel;
            const vector<size_t> &gps = groups.groups(qlev);
            assert(gps.size() == sel.size());
            for (size_t i = 0; i < sel.size(); ++i)
                groups.set_lev_select(gps[i], sel[i]);
        }
        ++profiler.cacheHits;
#ifndef NDEBUG
        cout << getSolverName(qlev) << " cache hit, prob = " << prob << endl;
#endif
        return true;
    }
    return false;
}

bool QestoGroups::record(size_t qlev, const vec<Lit> &parent_selection, double &prob)
{
    CacheEntry entry(parent_selection, prob);
    assert(sel_caches[qlev].find(entry) == sel_caches[qlev].end());

    if (levs.level_type(qlev) == EXISTENTIAL)
    {
        const vector<size_t> &gps = groups.groups(qlev);
        vector<bool> sel(gps.size());
        for (size_t i = 0; i < gps.size(); ++i)
            sel[i] = groups.is_lev_select(gps[i]);
        entry.set_selection(sel);
    }
#ifndef NDEBUG
    cout << getSolverName(qlev) << " cache store, prob = " << prob << endl;
#endif

    return sel_caches[qlev].insert(entry).second;
}

void QestoGroups::remove_duplicate_lits(size_t qlev, vec<Lit> &cla)
{
    Lit p;
    int i, j;

    sort(cla);
    for (i = j = 0, p = lit_Undef; i < cla.size(); ++i)
        if (abstractions[qlev].value(cla[i]) != l_False && cla[i] != p)
            cla[j++] = p = cla[i];
    cla.shrink(i - j);
}

void QestoGroups::output_ssat_sol(bool interrupted)
{
    bool timeout = profiler.is_timeout();
    double sol = get_ret_prob(0);
    std::pair<double, double> bounds;
    if (timeout || interrupted)
        bounds = levs.level_type(0) == EXISTENTIAL ? std::make_pair(sol, 1.0) : calculate_prob(0, prob2Learnts[0], true);
    else
        bounds = std::make_pair(sol, sol);

    printf("==== SSAT Final Result ====\n\n");
    if (timeout)
        printf("  > TIMEOUT!!\n");
    if (interrupted)
        printf("  > INTERRUPTED!!\n");
    printf("  > %s solution\n", (bounds.first == bounds.second ? "Exact" : "Approximate"));
    printf("  > Upper bound = %e\n", bounds.second);
    printf("  > Lower bound = %e\n", bounds.first);
    printf("  > Time        = %lf\n", profiler.get_tot_time());
    printf("\n");
}

/*********************************************************/
/************* Incremental Model Counting ****************/
/*********************************************************/

// build selection relation into cnf without enable variables
void QestoGroups::to_dimacs(FILE *f, size_t qlev)
{

    size_t cnt = 0;
    Var max = 1;
    vec<bool> encoded_group;

    vector<Var>& map = level_map[qlev];
    bool is_last = qlev==(levs.lev_count()-1);

    for (size_t gi : groups.groups(qlev))
    {
        if (!check_and_encode(encoded_group, gi)){
            {
                const LitSet &ls = groups.lits(gi);
                cnt += ls.size() + 1;
                // Map vars to 0 ~ max
                FOR_EACH(li, ls)
                mapVar(var(*li), map, max);
                mapVar(t(qlev, gi), map, max);
            }
        }
    }
    level_maxV[qlev] = max-1;

    fprintf(f, "p cnf %d %ld\n", max - 1, cnt);


    // write selection relation
    for (int gi = 0; gi < encoded_group.size(); ++gi)
    {
        if (encoded_group[gi])
        {
            const LitSet &ls = groups.lits(gi);
            Var tvar = t(qlev, gi);

            FOR_EACH(li, ls)
            fprintf(f, "-%d %s%d 0\n", map[tvar], sign(*li) ? "" : "-", map[var(*li)]);
            FOR_EACH(li, ls)
            fprintf(f, "%s%d ", sign(*li) ? "-" : "", map[var(*li)]);
            fprintf(f, "%d 0\n", map[tvar]);
        }
    }
}


// build cnf with enable variables
void QestoGroups::to_dimacs_cnf_en(FILE* f, size_t qlev, const ProbMap& prob2Learnt, vec<Var>& map, size_t& en_var_offset)
{
    // cout << "Writing cnf file ..." << endl;
    size_t cls_cnt = 0, gi, en_var_cnt = 0;
    Var max = 1;
    vec<bool> encoded_group;
    bool selected;

    // map grp/var id to variable in cnf
    for(auto it : prob2Learnt)
    {
        en_var_cnt += 1;
        for (const vector<EncGrp> &enc_groups : it.second)
        {
            if (enc_groups.empty())
            {
                fprintf(f, "p cnf 1 2\n1 0\n-1 0\n");
                return;
            }
            cls_cnt += 1;
            for (EncGrp enc_gi : enc_groups)
            {
                gi = get_group(enc_gi);

                if (!check_and_encode(encoded_group, gi))
                {
                    const LitSet &ls = groups.lits(gi);
                    cls_cnt += ls.size() + 1;
                    // Map vars to 0 ~ max
                    FOR_EACH(li, ls) mapVar(var(*li), map, max);                    
                    mapVar(t(qlev, gi), map, max);
                }
            }
        }
    }

    en_var_cnt = prob2Learnt.size(); // enable variable count
    en_var_offset = map.size();      // enable variable offset
    // map enable variable
    // cout << "Enable Var Offset is " << en_var_offset << endl;
    for(size_t i=0; i<en_var_cnt; ++i){
        mapVar(i+en_var_offset, map, max);
        // cout << "Map var " << i+en_var_offset << " to " << max << endl;
    }

    fprintf(f, "p cnf %d %ld\n", max - 1, cls_cnt);

    // write selection relation
    for (int gi = 0; gi < encoded_group.size(); ++gi)
    {
        if (encoded_group[gi])
        {
            const LitSet &ls = groups.lits(gi);
            Var tvar = t(qlev, gi);
            FOR_EACH(li, ls)
            fprintf(f, "-%d %s%d 0\n", map[tvar], sign(*li) ? "" : "-", map[var(*li)]);
            FOR_EACH(li, ls)
            fprintf(f, "%s%d ", sign(*li) ? "-" : "", map[var(*li)]);
            fprintf(f, "%d 0\n", map[tvar]);
        }
    }

    size_t en_var_id = 0;
    // write learnt clause with enable variable
    for(auto it : prob2Learnt)
    {
        for (const vector<EncGrp> &enc_groups : it.second)
        {
            fprintf(f, "-%d ", map[en_var_id+en_var_offset]);
            for (EncGrp enc_gi : enc_groups)
            {
                gi = get_group(enc_gi);
                selected = get_select(enc_gi);
                Var tvar = t(qlev, gi);
                fprintf(f, "%s%d ", selected ? "" : "-", map[tvar]);
            }
            fprintf(f, "0\n");
        }
        en_var_id ++;
    }

}

//TODO compile cnf w/wo enable variable
void QestoGroups::compile_cnf_to_nnf(size_t qlev, bool en)
{
    // compile cnf to dnnf to LAST_LEVEL_NNF using d4
    // cout << "Compiling cnf to nnf ..." << endl;
    profiler.set_WMC_time();
    char cmd[1024];
    if(!en) // last level
        sprintf(cmd, "%s %s.%d -out=%s.%d > /dev/null",dDNNF_COMPILER, LEVEL_CNF, qlev, LEVEL_NNF, qlev);
    else
        sprintf(cmd, "%s %s -out=%s > %s > /dev/null",dDNNF_COMPILER, CNF_FILE, NNF_FILE, SATPROB_FILE);
    system(cmd);
    profiler.accum_WMC_time();
    // cout << "After calling d4 ..." << endl;
}

// assumption based WMC, without enable variables
double QestoGroups::assump_level_wmc(size_t qlev, const vector<vector<EncGrp>> &enc_learnts)
{
    // cout << "Assump level MC ..." << endl;
    profiler.WMCCnt++;
    profiler.AssumpMCCnt++;
    DNNFCounter& counter = level_counter[qlev];
    vector<Var>& map = level_map[qlev];

    //FIXME add previous level selection into assumption, if !last_lev
    bool is_last_lev = (qlev == (levs.lev_count()-1));

    if (!counter.is_created())
    {
        // counter not yet created
        // cout << "Created??" << endl;
        string level_cnf_file = LEVEL_CNF, level_nnf_file = LEVEL_NNF;
        level_cnf_file.append(".").append(to_string(qlev));
        level_nnf_file.append(".").append(to_string(qlev));
        FILE *f_cnf = fopen(level_cnf_file.c_str(), "w");
        to_dimacs(f_cnf, qlev);
        fclose(f_cnf);

        compile_cnf_to_nnf(qlev); // level compile

        ifstream f_nnf(level_nnf_file.c_str());
        counter = DNNFCounter(f_nnf);
        f_nnf.close();

        // set weights

        const vector<double> &probs = levs.get_probs();
        // cout << "MaxV " << level_maxV[qlev] << endl;
        for (size_t i = 0; i < map.size(); ++i)
        {
            //cout << i << " " << map[i] << endl;
            if (map[i] == -1 ){
                if(i <= level_maxV[qlev]){ // unused variable
                    //counter.set_lit_weight(i, 0);
                    //cout << "Set Lit " << i << " weight " << 0 << endl;
                }
                continue;
            }
            //assert(i >= probs.size() || probs[i] != -1);
            if ( i < probs.size() ){
                counter.set_lit_weight(map[i], probs[i]);
                // cout << "Set Lit " << map[i] << " weight " << probs[i] << endl;
            }
        }
    }


    vector<int> assumps;
    if(is_last_lev){
        // cout << "Last Level???" << endl;
        assumps.resize(enc_learnts.size());
        size_t idx = 0;
        for (const vector<EncGrp> &enc_groups : enc_learnts)
        {
            if (enc_groups.empty())
            {
                return 0;
            }
            assert(enc_groups.size()==1);
            size_t gi = get_group(enc_groups[0]);
            assumps[idx] = -map[t(qlev, gi)] ;
            ++idx;
        }
    }
    else{
        // cout << "Assump???" << enc_learnts.size() << endl;
        assert(enc_learnts.size()==1);
        vector<EncGrp> enc_groups;

        enc_groups = enc_learnts[0];
        if(enc_groups.empty()) return 1;

        assumps.resize(enc_groups.size());
        for(size_t idx=0; idx<enc_groups.size(); ++idx){
            // cout << "mep1" << endl;
            size_t gi = get_group(enc_groups[idx]);
            // cout << "mep2" << endl;
            assumps[idx] =  get_select(enc_groups[idx]) ? -map[t(qlev, gi)] : map[t(qlev, gi)];
            // cout << "Assume " << assumps[idx] << endl;
        }
    }
    return counter.assump_model_count(assumps);
    
}

double QestoGroups::incre_calculate_prob(size_t qlev, const ProbMap& prob2Learnt, bool has_thres, double thres)
{

    // TODO seperate learntSize=1 and learntSize!=1 into 2 prob2Learnt map: pmap1 and pmap2
    //      apply increMC w.  enable on pmap2 if pmap2.size()>=2
    //      apply increMC wo. enable on pmap2 , O.W.
    //      apply increMC wo. enable on pmap1
    ProbMap pmap1, pmap2;
    for(auto it : prob2Learnt){
        // cout << it.first << " " << it.second.size() << endl;
        if(it.second.size()==1)
            pmap1[it.first] = it.second; // learnts size==1
        else
            pmap2[it.first] = it.second; // learnts size>1
    }


    double accum = 0, sel_prob, left = 1; // accum <= ret <= accum+left

    // cout << "Incremental MC at lev" << qlev << " size1 / size2 = " << pmap1.size() << " / " << pmap2.size() << endl;

    // pmap1 incremental(assump) Model counting
    // TODO
    for (auto it : pmap1)
    {   
        //assert(accum >= 0 && it.first >= 0 && left >= 0);
        if ( it.first == 0)
            continue;
        // if (accum + it.first * left < get_ret_prob((int)qlev - 1))
        //     return -1;
        assert(it.second.size()==1);

        // cout << "Where" << endl;
        double p = assump_level_wmc(qlev, it.second);
        sel_prob = p;

        assert(sel_prob >= 0 && sel_prob <= 1);

        accum += it.first * sel_prob;
        left -= sel_prob;

        // if(has_thres){
        //     if(accum >= thres)
        //         return accum;
        //     if(accum+left < thres)
        //         return accum+left;
        // }
    }

    // cout << "After pmap1 " << accum << endl; 


    // pmap2
    if( pmap2.size() == 1){ // original Model Counting
        accum += calculate_prob(qlev, pmap2).first;
    }
    else if(!pmap2.empty()){                   // Incrmental Model Counting with enable variable
        // write cnf
        FILE* f_cnf = fopen(CNF_FILE, "w");
        vec<Var> map;
        size_t en_var_offset;
        profiler.set_WMCIO_time();
        to_dimacs_cnf_en(f_cnf, qlev, pmap2, map, en_var_offset);
        profiler.accum_WMCIO_time();
        fclose(f_cnf);

        // compile cnf
        compile_cnf_to_nnf(qlev, true);

        // successive incremental model count

        ifstream f_nnf(NNF_FILE);
        if( is_file_empty(f_nnf) ) // unsat formula
            return 1;
        DNNFCounter model_counter(f_nnf);
        f_nnf.close();

        const vector<double> &probs = levs.get_probs();

        // set random weights
        for (size_t i=0; i<en_var_offset; ++i){
            if (map[i] == -1)
                continue;
            //assert(i >= probs.size() || probs[i] != -1);
            if ( i < probs.size() ){
                assert(levs.type(i)==RANDOM);
                model_counter.set_lit_weight(map[i], probs[i]);  
            }      
        }

        vector<int> assumps(pmap2.size());

        for(size_t i=0; i<assumps.size(); ++i)
            assumps[i] = -map[ (map.size()-1)-i];

        size_t en_var_id = 0;
        for (auto it : pmap2)
        {   
            //assert(accum >= 0 && it.first >= 0 && left >= 0);
            if ( it.first == 0)
                continue;
            if (accum + it.first * left < get_ret_prob((int)qlev - 1))
                return -1;

            profiler.WMCCnt++;
            profiler.AssumpMCCnt++;

            *(assumps.end()-1) = -assumps.back(); // enable the corresponding learnt clause
            profiler.set_MCQ_time();
            double p = model_counter.assump_model_count(assumps);
            profiler.accum_MCQ_time();

            sel_prob = 1 - p;

            profiler.set_MCS_time();
            model_counter.condition_on( vector<int>{ -assumps.back() } );
            profiler.accum_MCS_time();
            assert(sel_prob >= 0 && sel_prob <= 1);
            assumps.pop_back();

            accum += it.first * sel_prob;
            left -= sel_prob;
            en_var_id ++;

            if(has_thres){
                if(accum >= thres)
                    return accum;
                if(accum+left < thres)
                    return accum+left;
            }
        }
        assert(assumps.size()==0);
    }

    // cout << "After pmap2 " << accum << endl;

    return accum;
}


bool check_and_encode(vec<bool> &encoded, Var v)
{
    if (encoded.size() <= v || !encoded[v])
    {
        encoded.growTo(v + 1, false);
        encoded[v] = true;
        return false;
    }
    return true;
}

Var mapVar(Var v, vec<Var> &map, Var &max)
{
    if (map.size() <= v || map[v] == -1)
    {
        map.growTo(v + 1, -1);
        // cout << "Map " << v << " to " << max << endl;
        map[v] = max++;
    }
    return map[v];
}

Var mapVar(Var v, vector<Var> &map, Var &max)
{
    if (map.size() <= v){
        map.resize(v + 1, -1);
        map[v] = max++;
    }
    else if(map[v]==-1){
        map[v] = max++;
    }
    return map[v];
}

void concat_assumptions(vec<Lit> &concat, vec<Lit> &assump1, vec<Lit> &assump2)
{
    concat.clear();
    concat.capacity(assump1.size() + assump2.size());
    for (int i = 0; i < assump1.size(); ++i)
        concat.push(assump1[i]);
    for (int i = 0; i < assump2.size(); ++i)
        concat.push(assump2[i]);
}

void print_encgrps(const vector<EncGrp> &enc_groups)
{
    cout << "( ";
    for (EncGrp enc_gi : enc_groups)
        cout << get_group(enc_gi) << (get_select(enc_gi) ? "" : "\'") << ' ';
    cout << ")";
}

bool is_file_empty(std::ifstream& f){
    return f.peek() == std::ifstream::traits_type::eof();
}
