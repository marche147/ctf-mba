#pragma once

#include "util/params.h"

class ast_manager;
class tactic;

tactic * mk_mba_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
    ADD_TACTIC("mba", "Toy MBA simplifier", "mk_mba_tactic(m, p)")
*/