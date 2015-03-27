(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2015 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)


(*i camlp4deps: "grammar/grammar.cma" i*)

DECLARE PLUGIN "equations_plugin"

open Equations_common
open Extraargs
open Eauto
open Locusops
open Term
open Names
open Tactics
open Pp
open Nameops
open Refiner
open Errors
open Constrexpr

TACTIC EXTEND decompose_app
[ "decompose_app" ident(h) ident(h') constr(c) ] -> [ 
  Proofview.Goal.enter (fun gl ->
    let f, args = decompose_app c in
    let fty = Tacmach.New.pf_type_of gl f in
    let flam = mkLambda (Name (id_of_string "f"), fty, mkApp (mkRel 1, Array.of_list args)) in
      (Proofview.tclTHEN (letin_tac None (Name h) f None allHyps)
  	 (letin_tac None (Name h') flam None allHyps)))
  ]
END


(* TACTIC EXTEND abstract_match *)
(* [ "abstract_match" ident(hyp) constr(c) ] -> [ *)
(*   match kind_of_term c with *)
(*   | Case (_, _, c, _) -> letin_tac None (Name hyp) c None allHypsAndConcl *)
(*   | _ -> tclFAIL 0 (str"Not a case expression") *)
(* ] *)
(* END *)

(* TACTIC EXTEND autounfold_first *)
(* | [ "autounfold_first" hintbases(db) "in" hyp(id) ] -> *)
(*     [ autounfold_first (match db with None -> ["core"] | Some x -> x) (Some (id, InHyp)) ] *)
(* | [ "autounfold_first" hintbases(db) ] -> *)
(*     [ autounfold_first (match db with None -> ["core"] | Some x -> x) None ] *)
(* END *)

(* Sigma *)


VERNAC COMMAND EXTEND Derive_Signature CLASSIFIED AS QUERY
| [ "Derive" "Signature" "for" constr(c) ] -> [ 
  let c', _ = Constrintern.interp_constr (Global.env ()) (Evd.from_env (Global.env())) c in
    match kind_of_term c' with
    | Ind (i,_) -> ignore(Sigma.declare_sig_of_ind (Global.env ()) i)
    | _ -> Errors.error "Expected an inductive type"
  ]
END

TACTIC EXTEND get_signature_pack
[ "get_signature_pack" hyp(id) ident(id') ] -> [ 
  Proofview.Goal.enter (fun gl ->
    let gl = Proofview.Goal.assume gl in
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let sigsig, sigpack = Sigma.get_signature env sigma (Tacmach.New.pf_get_hyp_typ id gl) in
      letin_tac None (Name id') (mkApp (sigpack, [| mkVar id |])) None nowhere) ]
END
      
TACTIC EXTEND pattern_sigma
[ "pattern" "sigma" hyp(id) ] -> [
  Proofview.Goal.enter (fun gl ->
    let gl = Proofview.Goal.assume gl in
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let decl = Tacmach.New.pf_get_hyp id gl in
    let term = Option.get (Util.pi2 decl) in
      Sigma.pattern_sigma term id env sigma) ]
END
TACTIC EXTEND curry
[ "curry" hyp(id) ] -> [ 
  let open Tacmach in
  Proofview.V82.tactic 
    (fun gl ->
      match Sigma.curry_hyp (project gl) (mkVar id) (pf_get_hyp_typ gl id) with
      | Some (prf, typ) -> 
	tclTHENFIRST (Proofview.V82.of_tactic (assert_before_replacing id typ))
	  (Tacmach.refine_no_check prf) gl
      | None -> tclFAIL 0 (str"No currying to do in" ++ pr_id id) gl) ]
END

(* TACTIC EXTEND pattern_tele *)
(* [ "pattern_tele" constr(c) ident(hyp) ] -> [ fun gl -> *)
(*   let settac = letin_tac None (Name hyp) c None onConcl in *)
(*     tclTHENLIST [settac; pattern_sigma c hyp] gl ] *)
(* END *)

(* Depelim *)

TACTIC EXTEND dependent_pattern
| ["dependent" "pattern" constr(c) ] -> [ 
  Proofview.V82.tactic (Depelim.dependent_pattern c) ]
END

TACTIC EXTEND dependent_pattern_from
| ["dependent" "pattern" "from" constr(c) ] ->
    [ Proofview.V82.tactic (Depelim.dependent_pattern ~pattern_term:false c) ]
END


(* TACTIC EXTEND dependent_generalize *)
(* | ["dependent" "generalize" hyp(id) "as" ident(id') ] ->  *)
(*     [ fun gl -> generalize_sigma (pf_env gl) (project gl) (mkVar id) id' gl ] *)
(* END *)
(* TACTIC EXTEND dep_generalize_force *)
(* | ["dependent" "generalize" "force" hyp(id) ] ->  *)
(*     [ abstract_generalize ~generalize_vars:false ~force_dep:true id ] *)
(* END *)
(* TACTIC EXTEND dependent_generalize_eqs_vars *)
(* | ["dependent" "generalize" "vars" hyp(id) ] ->  *)
(*     [ abstract_generalize ~generalize_vars:true id ] *)
(* END *)
(* TACTIC EXTEND dependent_generalize_eqs_vars_force *)
(* | ["dependent" "generalize" "force" "vars" hyp(id) ] ->  *)
(*     [ abstract_generalize ~force_dep:true ~generalize_vars:true id ] *)
(* END *)

TACTIC EXTEND needs_generalization
| [ "needs_generalization" hyp(id) ] -> 
    [ Proofview.V82.tactic (fun gl -> 
      if Depelim.needs_generalization gl id 
      then tclIDTAC gl
      else tclFAIL 0 (str"No generalization needed") gl) ]
END

(* Equations *)

open Extraargs
TACTIC EXTEND solve_equations
  [ "solve_equations" tactic(destruct) tactic(tac) ] -> 
  [ of82 (Equations.solve_equations_goal (to82 (Tacinterp.eval_tactic destruct)) (to82 (Tacinterp.eval_tactic tac))) ]
END

TACTIC EXTEND simp
| [ "simp" ne_preident_list(l) clause(c) ] -> 
    [ of82 (Equations.simp_eqns_in c l) ]
| [ "simpc" constr_list(l) clause(c) ] -> 
    [ of82 (Equations.simp_eqns_in c (Equations.dbs_of_constrs l)) ]
END


VERNAC COMMAND EXTEND Derive_NoConfusion CLASSIFIED AS QUERY
| [ "Derive" "NoConfusion" "for" constr_list(c) ] -> [ 
    List.iter (fun c ->
      let env = (Global.env ()) in
      let c',ctx = Constrintern.interp_constr env Evd.empty c in
	match kind_of_term c' with
	| Ind i -> Equations.derive_no_confusion env (Evd.from_env ~ctx env) i
	| _ -> error "Expected an inductive type")
      c
  ]
END

(* let wit_r_equation_user_option : equation_user_option Genarg.uniform_genarg_type = *)
(*   Genarg.create_arg None "r_equation_user_option" *)

open Equations

ARGUMENT EXTEND equation_user_option
TYPED AS equation_user_option
PRINTED BY pr_r_equation_user_option
| [ "noind" ] -> [ OInd, false ]
| [ "ind" ] -> [ OInd, true ]
| [ "struct" ] -> [ ORec, true ]
| [ "nostruct" ] -> [ ORec, false ]
| [ "comp" ] -> [ OComp, true ]
| [ "nocomp" ] -> [ OComp, false ]
| [ "eqns" ] -> [ OEquations, true ]
| [ "noeqns" ] -> [ OEquations, false ]
END

ARGUMENT EXTEND equation_options
TYPED AS equation_options
PRINTED BY pr_equation_options
| [ "(" ne_equation_user_option_list(l) ")" ] -> [ l ]
| [ ] -> [ [] ]
END


module Gram = Pcoq.Gram
module Vernac = Pcoq.Vernac_
module Tactic = Pcoq.Tactic

type binders_let2_argtype =
    (Constrexpr.local_binder list *
     (Names.identifier located option * Constrexpr.recursion_order_expr))
    Genarg.uniform_genarg_type
type deppat_equations_argtype = pre_equation list Genarg.uniform_genarg_type

let wit_binders_let2 : binders_let2_argtype =
  Genarg.create_arg None "binders_let2"

let pr_raw_binders_let2 _ _ _ l = mt ()
let pr_glob_binders_let2 _ _ _ l = mt ()
let pr_binders_let2 _ _ _ l = mt ()

let binders_let2 : (local_binder list * (identifier located option * recursion_order_expr)) Gram.entry =
  Pcoq.create_generic_entry "binders_let2" (Genarg.rawwit wit_binders_let2)

let _ = Pptactic.declare_extra_genarg_pprule wit_binders_let2
  pr_raw_binders_let2 pr_glob_binders_let2 pr_binders_let2


let wit_deppat_equations : deppat_equations_argtype =
  Genarg.create_arg None "deppat_equations"

let pr_raw_deppat_equations _ _ _ l = mt ()
let pr_glob_deppat_equations _ _ _ l = mt ()
let pr_deppat_equations _ _ _ l = mt ()

let deppat_equations : pre_equation list Gram.entry =
  Pcoq.create_generic_entry "deppat_equations" (Genarg.rawwit wit_deppat_equations)

let _ = Pptactic.declare_extra_genarg_pprule wit_deppat_equations
  pr_raw_deppat_equations pr_glob_deppat_equations pr_deppat_equations

open Glob_term
open Util
open Pcoq
open Prim
open Constr
open G_vernac
open Compat
open Tok

GEXTEND Gram
  GLOBAL: pattern deppat_equations binders_let2;
 
  deppat_equations:
    [ [ l = LIST1 equation SEP ";" -> l ] ]
  ;

  binders_let2:
    [ [ l = binders -> l, (None, CStructRec)  ] ]
  ;

  equation:
    [ [ id = identref; 	pats = LIST1 patt; r = rhs -> (Some id, SignPats pats, r)
      | "|"; pats = LIST1 lpatt SEP "|"; r = rhs -> (None, RefinePats pats, r) 
    ] ]
  ;

  patt:
    [ [ id = smart_global -> !@loc, PEApp ((!@loc,id), [])
      | "_" -> !@loc, PEWildcard
      | "("; p = lpatt; ")" -> p
      | "?("; c = Constr.lconstr; ")" -> !@loc, PEInac c
      | p = pattern LEVEL "0" -> !@loc, PEPat p
    ] ]
  ;

  lpatt:
    [ [ id = smart_global; pats = LIST0 patt -> !@loc, PEApp ((!@loc,id), pats)
      | p = patt -> p
    ] ]
  ;

  rhs:
    [ [ ":=!"; id = identref -> Empty id
      |":="; c = Constr.lconstr -> Program c
      |"=>"; c = Constr.lconstr -> Program c
      | "with"; c = Constr.lconstr; ":="; e = equations -> Refine (c, e)
      | "<="; c = Constr.lconstr; "=>"; e = equations -> Refine (c, e)
      | "<-"; "(" ; t = Tactic.tactic; ")"; e = equations -> By (Inl t, e)
      | "by"; IDENT "rec"; id = identref; rel = OPT constr; [":="|"=>"]; e = deppat_equations -> Rec (id, rel, e)
    ] ]
  ;

  equations:
    [ [ "{"; l = deppat_equations; "}" -> l 
      | l = deppat_equations -> l
    ] ]
  ;

  END

VERNAC COMMAND EXTEND Define_equations CLASSIFIED AS QUERY
| [ "Equations" equation_options(opt) ident(i) binders_let2(l) 
      ":" lconstr(t) ":=" deppat_equations(eqs)
      (* decl_notation(nt) *) ] ->
    [ Equations.equations opt (dummy_loc, i) l t [] eqs ]
      END

VERNAC COMMAND EXTEND Derive_DependentElimination CLASSIFIED AS QUERY
| [ "Derive" "DependentElimination" "for" constr_list(c) ] -> [ 
    List.iter (fun c ->
      let c',ctx = Constrintern.interp_constr (Global.env ()) Evd.empty c in
	match kind_of_term c' with
	| Ind i -> ignore(Equations.derive_dep_elimination ctx i dummy_loc) (* (Glob_ops.loc_of_glob_constr c)) *)
	| _ -> error "Expected an inductive type")
      c
  ]
END

(* TACTIC EXTEND block_goal *)
(* [ "block_goal" ] -> [ of82 ( *)
(*   (fun gl -> *)
(*     let block = Lazy.force coq_block in *)
(*     let concl = pf_concl gl in *)
(*     let ty = pf_type_of gl concl in *)
(*     let evd = project gl in *)
(*     let newconcl = mkApp (block, [|ty; concl|]) in *)
(*     let evd, _ty = Typing.e_type_of (pf_env gl) evd newconcl in *)
(*       (\* msg_info (str "After e_type_of: " ++ pr_evar_map None evd); *\) *)
(*       tclTHEN (tclEVARS evd) *)
(* 	(convert_concl newconcl DEFAULTcast) gl)) ] *)
(* END *)
  
(* TACTIC EXTEND pattern_call *)
(* [ "pattern_call" constr(c) ] -> [ fun gl -> *)
(*   match kind_of_term c with *)
(*   | App (f, [| arg |]) -> *)
(*       let concl = pf_concl gl in *)
(*       let replcall = replace_term c (mkRel 1) concl in *)
(*       let replarg = replace_term arg (mkRel 2) replcall in *)
(*       let argty = pf_type_of gl arg and cty = pf_type_of gl c in *)
(*       let rels = [(Name (id_of_string "call"), None, replace_term arg (mkRel 1) cty); *)
(* 		  (Name (id_of_string "arg"), None, argty)] in *)
(*       let newconcl = mkApp (it_mkLambda_or_LetIn replarg rels, [| arg ; c |]) in *)
(* 	convert_concl newconcl DEFAULTcast gl  *)
(*   | _ -> tclFAIL 0 (str "Not a recognizable call") gl ] *)
(* END *)

TACTIC EXTEND pattern_call
[ "pattern_call" constr(c) ] -> [ of82 (pattern_call c) ]
END

(* Subterm *)

VERNAC COMMAND EXTEND Derive_Subterm CLASSIFIED AS QUERY
| [ "Derive" "Subterm" "for" constr(c) ] -> [ 
    let c',_ = Constrintern.interp_constr (Global.env ()) Evd.empty c in
      match kind_of_term c' with
      | Ind i -> Subterm.derive_subterm i
      | _ -> error "Expected an inductive type"
  ]
END

VERNAC COMMAND EXTEND Derive_Below CLASSIFIED AS QUERY
| [ "Derive" "Below" "for" constr(c) ] -> [ 
  let c', ctx = Constrintern.interp_constr (Global.env ()) Evd.empty c in
    match kind_of_term c' with
    | Ind i -> Subterm.derive_below ctx i
    | _ -> error "Expected an inductive type"
  ]
END

(* Eqdec *)

VERNAC COMMAND EXTEND Derive_EqDec CLASSIFIED AS QUERY
| [ "Derive" "Equality" "for" constr_list(c) ] -> [ 
    List.iter (fun c ->
      let c', _ = Constrintern.interp_constr (Global.env ()) Evd.empty c in
	match kind_of_term c' with
	| Ind i -> Eqdec.derive_eq_dec i
	| _ -> error "Expected an inductive type")
      c
  ]
END
