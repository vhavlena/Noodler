import awalipy
import itertools

### Comments ###
# Currently, I work with lists of automata for each side
# Perhaps a dict var → automaton + equation sides would
# be a better fit: we do not create copies of the automata.
# Caveats are that the dictionary can evolve over time.
#
# Next, when splitting a segment automaton into segments
# I only trim the automata. Minimization can be run.

###
# make segment_automaton function that takes sequenc of vars
# and automata_dictionary.
###

    #TODO: Rename
def automata_for_vars(var_sequence, re_dict, alphabet):
    """
    Create automata for sequence of variables.
    
    For a sequence of variables ``x1, … , xn`` and a dictionary
    that maps variables to regular expressions (REs) create a 
    sequence of automata ``a1, … , an`` that represent the 
    corresponding languages given by the REs. This is,
    ``ai`` represents the language of ``re_dict[xi]``.
    
    If one variable occurs multiple times in the sequence, the
    distinct automata are different objects.
    
    Parameters
    ----------
    var_sequence : str or list of str
        Define the sequence of variable names. 
        Str can be used only if variable names are characters.
    re_dict : dict [str → str]
        Maps variable names to regular expressions
    alphabet : str
        Alphabet of the regular expressions
    
    Returns
    -------
    automata : list of awali automata
        Automaton ``ai`` represents the language of ``re_dict[xi]``.
    """
    automata = []
    for var in var_sequence:
        re_str = re_dict[var]
        re = awalipy.RatExp(re_str, alphabet=alphabet)
        automata.append(re.exp_to_aut())
    return automata

def union_multi(automata):
    """
    Make union of multiple automata.
    
    Parameters
    ----------
    automata : list of auts
        Must be non-empty.
        All automata must use the same alphabet.
        
    Returns
    -------
    aut
        parallel union of auts in ``automata``
    """
    res = awalipy.make_automaton(automata[0].alphabet())
    for aut in automata:
        res.union_here(aut)

    return res

def chain_automata(automata):
    """
    Chain sequence of auts into aut for concatenation.
    
    Connect the automata in the sequence by ε-transitions. For
    ``a_1, a_2, … , a_n`` create automaton A that represents the
    language L(A) = L(a_1) · L(a_2) · … · L(a_n). A is basically
    an union of ``a_1 … a_n`` as they are, connected with
    ε-transitions. Each final state of ``a_i`` is connected by
    an ε-transition with each initial state of ``a_{i+1}
    
    Parameters
    ----------
    automata : list of auts
        Must be non-empty
    
    Returns
    -------
    A : aut 
        Automaton that links auts from ``automata`` by ε-transitions
        beteen final an inital states.
    """
    res = union_multi(automata)
    res.allow_eps_transition_here()
    
    # pre_a is the automaton which will be source of ε-transitions,
    # next_a is the automaton whose inital states receive the ε-tr.
    # offsets keep the shift in automata numbers between res and 
    #   pre/next
    pre_a = automata[0]
    pre_offset = 0
    
    # 1. For each final of pre_a:
    #     I. add ε to next_a
    #     II. Unset final
    # 2. Unset init_states of next_a
    for next_a in automata[1:]:
        next_offset = pre_offset + len(pre_a.states())
        
        for final_pre in pre_a.final_states():
            final_res = pre_offset + final_pre
            
            # Add ε-transitions
            for init_next in next_a.initial_states():
                init_res = next_offset + init_next
                res.add_eps_transition(final_res, init_res)              
            
            res.unset_final(final_res)
        
        for init_next in next_a.initial_states():
            init_res = next_offset + init_next
            res.unset_initial(init_res)
            
        pre_a = next_a
        pre_offset = next_offset
            
    return res

def eps_preserving_product(aut_l, aut_r, opts={}):
    """
    Intersection of ε-NFA with NFA.
    
    Create product of ``aut_l`` and ``aut_r``, where ``aut_l``
    can contain ε-transitions. The product preserves the 
    ε-transitions of ``aut_l``. This means, for each ε-trans
    of the form `s -ε-> p` and each product state `(s, a)`, an
    ε-transition `(s, a) -ε-> (p, a)` is created. 
    
    Parameters
    ----------
    aut_l : aut with ε-transitions
    aut_r : aut without ε-transitions
    
    Automata must share alphabets.
    
    Returns
    -------
    aut
        Product of ``aut_l`` with ``aut_r`` with ε-transitions
        preserved.
        
    Notes
    -----
    Currently inefficient! It builds all pairs of states and
    only later trims the automaton. We should build only the
    reachable part to speed things up.
    """
    names = opts.get("history", False)
    
    state_map = {}
    alphabet = aut_l.alphabet()
    new_aut = awalipy.make_automaton(alphabet)
    new_aut.allow_eps_transition_here()
    
    # Create states
    for s in aut_l.states():
        for t in aut_r.states():
            if names:
                st = new_aut.add_state(f"{aut_l.get_state_name(s)} | {aut_r.get_state_name(t)}")
            else:
                st = new_aut.add_state()
            state_map[s,t] = st
            if aut_l.is_final(s) and aut_r.is_final(t):
                new_aut.set_final(st)
            if aut_l.is_initial(s) and aut_r.is_initial(t):
                new_aut.set_initial(st)
                
    for sl in aut_l.states():
        for sr in aut_r.states():
            for a in alphabet:
                for tl in aut_l.outgoing(sl,a):
                    dstl = aut_l.dst_of(tl)
                    for tr in aut_r.outgoing(sr,a):
                        dstr = aut_r.dst_of(tr)
                        new_aut.set_transition(state_map[sl,sr], state_map[dstl,dstr], a)
                        
            for tl in aut_l.outgoing(sl, "\e"):
                dstl = aut_l.dst_of(tl)
                new_aut.add_eps_transition(state_map[sl,sr], state_map[dstl,sr])
    new_aut.trim_here()
    
    return new_aut

def one_sided_product(chain_l, chain_r, opts={}):
    aut_r = chain_r.minimal_automaton()
    
    return eps_preserving_product(chain_l, aut_r, opts)

def eps_segmentation(aut):
    """
    Compute depth of ε-transitions.

    This works only for segment-automata. These are automata
    whose state space can be split into several segments
    connected by ε-transitions in a chain. No other 
    ε-transitions are allowed. As a consequence, no ε-trans.
    can appear in a cycle.

    Parameters
    ----------
    aut : aut
        Segment automaton.
        
    Returns
    -------
    depths : dict of lists of ε-transitions
        For each depth i we have that depths[i] contains a list
        of ε-transitions of depth `i`.
    """
    depths = {}
    
    # store already visited states
    visited = {}
    for i in aut.states():
        visited[i] = False

    to_do = []
    for s in aut.initial_states():
        to_do.append((s, 0))
        
    while len(to_do) > 0 :
        state, depth = to_do.pop()
        if not (visited[state]):
            visited[state] = True
            out_trs = aut.outgoing(state)
            for tr in out_trs:
                if aut.label_of(tr) == "\e":
                    depths.setdefault(depth, [])
                    depths[depth].append(tr)
                    to_do.append((aut.dst_of(tr), depth+1))
                else:
                    to_do.append((aut.dst_of(tr), depth))
    
    return depths

def noodlify(aut, include_empty=False):
    """
    Create noodles from segment automaton.
    
    Segment automaton is a chain of automata connected
    via ε-transitions. A noodle is a copy of the segment
    automaton with exactly 1 ε-transition between each
    two consecutive segments. Noodlify return the list of
    all (non-empty) noodles.
    
    Parameters
    ----------
    aut : aut
        Segment automaton to noodlify.
    include_empty : Bool (default False)
        Include also empty noodels if True.
    """
    # Stores the noodles
    noodles = []
    
    # We need to make a copy of the automaton before running
    # segmentation to remove non-existent transitions.
    aut = aut.copy()
    # depth → list of ε-trans
    segments = eps_segmentation(aut)
    
    # For each combination of ε-transitions, create the automaton.
    for noodle_trans in itertools.product(*segments.values()):
        noodle = aut.copy()
        for i in reversed(range(len(noodle_trans))):
            # Remove all ε-tr. of depth i but noodle_trans[i]
            for tr in segments[i]:
                assert noodle.label_of(tr) == "\e"
                if tr != noodle_trans[i]:
                    noodle.del_transition(tr)
        
        noodle = noodle.trim()
        if include_empty or noodle.num_states() > 0:
            noodles.append(noodle)
   
    return noodles

def split_segment_aut(aut):
    """
    Splits segment automaton into segments.
    
    Returns a list of segments for aut in the order
    from left (initial state in segment automaton) to
    right (final states of segment automaton).
    
    Parameters
    ----------
    aut : aut
        Segment-automaton
    
    Returns
    -------
    list of auts
        Segments of ``aut``
    """
    # We need to make a copy before eps_segmentation
    # otherwise the trans_id could not match. We destroy
    # this automaton anyway in the process...
    aut = aut.copy()
    eps_trans = eps_segmentation(aut)
    
    segments = [aut.copy() for depth in eps_trans]
    segments.append(aut.copy())
    
    for depth, trans in eps_trans.items():
        # Split the left segment from aut into new_segment.
        for tr in trans:
            assert aut.label_of(tr) == "\e"
            assert segments[depth].label_of(tr) == "\e"
            segments[depth].set_final(aut.src_of(tr))
            segments[depth].del_transition(tr)
            for i in range(depth+1, len(segments)):
                segments[i].del_transition(tr)
                segments[i].set_initial(aut.dst_of(tr)) 
            #aut.set_initial(aut.dst_of(tr))                
            #aut.del_transition(tr)
        
    return [seg.trim() for seg in segments]

def unify(eq_l, eq_r, auts_l, auts_r, **kwargs):
    """
    Unify automata system for string equation.
    
    The equation is given as ``eq_l = eq_r`` and the
    system consists of two list of automata. Each 
    automaton in ``auts_l`` must correspond to a 
    variable in ``eq_l`` and anaogously for ``_r``.
    
    For each variable from ``eq_l`` and ``eq_r`` make
    an intersection of all automata corresponding to
    this variable. If x is at position 2 in ``eq_l``
    and at positions 0 and 3 in ``eq_r``, unify makes
    product of ``auts_l[2]`` with ``auts_r[0]`` and
    ``auts_r[3]``.
    
    Parameters
    ----------
    eq_l, eq_r : str or list of str
    auts_l, auts_r : list of auts
        Length of auts_l must agree with length of eq_l
    make_copies : Bool (default False)
        Do not share the automata for each variable, make
        copies instead, if True.
    Returns
    -------
    new_auts_l, new_auts_r : list of auts
        List of automata where automata representing
        the same variable are the same.
    """
    if len(auts_l) != len(eq_l):
        raise ValueError(f"""
        The length of `auts_l` must agree with length of `eq_l`.
        Given len(auts_l) = {len(auts_l)} and len(eq_l) = {len(eq_l)}.""")
    if len(auts_r) != len(eq_r):
        raise ValueError(f"""
        The length of `auts_r` must agree with length of `eq_r`.
        Given len(auts_r) = {len(auts_r)} and len(eq_r) = {len(eq_r)}.""")
    
    make_copies = kwargs.get("make_copies", False)
        
    variables = set(eq_l).union(set(eq_r))
    res_l = list(auts_l)
    res_r = list(auts_r)
    
    for var in variables:
        indices_l = [i for i, v in enumerate(eq_l) if v == var]
        indices_r = [i for i, v in enumerate(eq_r) if v == var]
        
        if len(indices_l) + len(indices_r) <= 1:
            continue
        
        automata = []
        for i in indices_l:
            # Call to proper changes the automata not to contain
            # ε-transitions. This is needed for product to work
            # in Awali.
            automata.append(auts_l[i].proper().min_quotient())
        for i in indices_r:
            automata.append(auts_r[i].proper().min_quotient())
        
        var_aut = automata[0]
        for next_aut in automata[1:]:
            var_aut = awalipy.product(var_aut, next_aut).min_quotient()
        
        for i in indices_l:
            if make_copies:
                res_l[i] = var_aut.copy()
            else:
                res_l[i] = var_aut
        for i in indices_r:
            if make_copies:
                res_r[i] = var_aut.copy()
            else:
                res_r[i] = var_aut
                
    return res_l, res_r