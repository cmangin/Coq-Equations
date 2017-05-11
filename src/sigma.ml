(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2016 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

open Cases
open Util
open Names
open Nameops
open Term
open Termops
open Declarations
open Inductiveops
open Environ
open Context
open Vars
open Reductionops
open Typeops
open Type_errors
open Pp
open Proof_type
open Errors
open Glob_term
open Retyping
open Pretype_errors
open Evarutil
open Evarconv
open List
open Libnames
open Topconstr
open Coqlib
open Globnames
open Tactics
open Refiner
open Tacticals
open Tacmach
open Decl_kinds
open Equations_common

let mkConstructG c u =
  mkConstructU (destConstructRef (Lazy.force c), u)

let mkIndG c u =
  mkIndU (destIndRef (Lazy.force c), u)

let mkConstG c u =
  mkConstU (destConstRef (Lazy.force c), u)

let mkAppG evd gr args = 
  let c = e_new_global evd gr in
    mkApp (c, args)

let applistG evd gr args = 
  mkAppG evd gr (Array.of_list args)

let mkSig evd (n, c, t) = 
  let args = [| c; mkLambda (n, c, t) |] in
    mkAppG evd (Lazy.force coq_sigma) args

let constrs_of_coq_sigma env evd t alias = 
  let rec aux env proj c ty =
    match kind_of_term c with
    | App (f, args) when is_global (Lazy.force coq_sigmaI) f && 
	                   Array.length args = 4 ->
       let ty = Retyping.get_type_of env !evd args.(1) in
	(match kind_of_term ty with
	| Prod (n, b, t) ->
	    let p1 = mkProj (Lazy.force coq_pr1, proj) in
	    let p2 = mkProj (Lazy.force coq_pr2, proj) in
	    (n, args.(2), p1, args.(0)) ::
              aux (push_rel (n, None, b) env) p2 args.(3) t
	| _ -> raise (Invalid_argument "constrs_of_coq_sigma"))
    | _ -> [(Anonymous, c, proj, ty)]
  in aux env alias t (Retyping.get_type_of env !evd t)

let decompose_coq_sigma t = 
  let s = Lazy.force coq_sigma in
    match kind_of_term t with
    | App (f, args) when is_global s f && Array.length args = 2 ->
       let ind, u = destInd f in
         Some (u, args.(0), args.(1))
    | _ -> None

let decompose_indapp f args =
  match kind_of_term f with
  | Construct ((ind,_),_)
  | Ind (ind,_) ->
      let (mib,mip) = Global.lookup_inductive ind in
      let first = mib.Declarations.mind_nparams_rec in
      let pars, args = Array.chop first args in
	mkApp (f, pars), args
  | _ -> f, args


(* let sigT_info = lazy (make_case_info (Global.env ()) (Globnames.destIndRef (Lazy.force sigT).typ) LetStyle) *)

let telescope evd = function
  | [] -> assert false
  | [(n, None, t)] -> t, [n, Some (mkRel 1), lift 1 t], mkRel 1
  | (n, None, t) :: tl ->
      let len = succ (List.length tl) in
      let ty, tys =
	List.fold_left
	  (fun (ty, tys) (n, b, t) ->
	    let pred = mkLambda (n, t, ty) in
	    let sigty = mkAppG evd (Lazy.force coq_sigma) [|t; pred|] in
            let _, u = destInd (fst (destApp sigty)) in
	      (sigty, (u, pred) :: tys))
	  (t, []) tl
      in
      let constr, _ = 
	List.fold_right (fun (u, pred) (intro, k) ->
	  let pred = Vars.lift k pred in
	  let (n, dom, codom) = destLambda pred in
	  let intro =
            mkApp (Universes.constr_of_global_univ
                     (Lazy.force coq_sigmaI, u), [| dom; pred; mkRel k; intro|]) in
	    (intro, succ k))
	  tys (mkRel 1, 2)
      in
      let (last, _, subst) = List.fold_right2
	(fun pred (n, b, t) (prev, k, subst) ->
	  let proj1 = mkProj (Lazy.force coq_pr1, prev) in
	  let proj2 = mkProj (Lazy.force coq_pr2, prev) in
	    (lift 1 proj2, succ k, (n, Some proj1, liftn 1 k t) :: subst))
	(List.rev tys) tl (mkRel 1, 1, [])
      in ty, ((n, Some last, liftn 1 len t) :: subst), constr

  | _ -> raise (Invalid_argument "telescope")

let sigmaize ?(liftty=0) env0 evd pars f =
  let env = push_rel_context pars env0 in
  let ty = Retyping.get_type_of env !evd f in
  let ctx, concl = splay_prod_assum env !evd ty in
  let argtyp, letbinders, make = telescope evd ctx in
    (* Everyting is in env, move to index :: letbinders :: env *) 
  let lenb = List.length letbinders in
  let pred =
    mkLambda (Name (id_of_string "index"), argtyp,
	     it_mkProd_or_LetIn
	       (mkApp (lift (succ lenb) f, 
		      rel_vect 0 lenb))
	       letbinders)
  in
  let tyargs = [| argtyp; pred |] in
  let tysig = mkAppG evd (Lazy.force coq_sigma) tyargs in
  let indexproj = Lazy.force coq_pr1 in
  let valproj = Lazy.force coq_pr2 in
  let indices = 
    (List.rev_map (fun l -> substl (tl l) (hd l)) 
     (Equations_common.proper_tails (map (fun (_, b, _) -> Option.get b) letbinders)))
  in
  let valsig =
    let argtyp = lift (succ lenb) argtyp in
    let pred = 
      mkLambda (Name (id_of_string "index"), argtyp,
	       it_mkProd_or_LetIn
		 (mkApp (lift (2 * succ lenb) f,
			rel_vect 0 lenb))
		 (Equations_common.lift_rel_contextn 1 (succ lenb) letbinders))
    in
    let _tylift = lift lenb argtyp in
      mkAppG evd (Lazy.force coq_sigmaI)
	[|argtyp; pred; lift 1 make; mkRel 1|]
  in
  let pred = it_mkLambda_or_LetIn pred pars in
  let _ = Typing.e_type_of env0 evd pred in
  let nf, _ = Evarutil.e_nf_evars_and_universes evd in
    (nf argtyp, nf pred, map_rel_context nf pars, List.map nf indices,
     indexproj, valproj, nf valsig, nf tysig)

let ind_name ind = Nametab.basename_of_global (Globnames.IndRef ind)

let signature_ref = lazy (init_reference ["Equations";"Signature"] "Signature")
let signature_sig = lazy (init_reference ["Equations";"Signature"] "signature")
let signature_pack = lazy (init_reference ["Equations";"Signature"] "signature_pack")

let signature_class evd =
  let evd, c = Evarutil.new_global evd (Lazy.force signature_ref) in
    evd, fst (snd (Option.get (Typeclasses.class_of_constr c)))

let build_sig_of_ind env sigma (ind,u as indu) =
  let (mib, oib as _mind) = Global.lookup_inductive ind in
  let ctx = inductive_alldecls indu in
  let lenpars = mib.mind_nparams_rec in
  let lenargs = List.length ctx - lenpars in
  if lenargs = 0 then
    user_err_loc (dummy_loc, "Derive Signature", 
		 str"No signature to derive for non-dependent inductive types");
  let args, pars = List.chop lenargs ctx in
  let parapp = mkApp (mkIndU indu, extended_rel_vect 0 pars) in
  let fullapp = mkApp (mkIndU indu, extended_rel_vect 0 ctx) in
  let evd = ref sigma in
  let idx, pred, pars, _, _, _, valsig, _ = 
    sigmaize env evd pars parapp 
  in
  let sigma = !evd in
    sigma, pred, pars, fullapp, valsig, ctx, lenargs, idx

let declare_sig_of_ind env sigma (ind,u) =
  let sigma, pred, pars, fullapp, valsig, ctx, lenargs, idx =
    build_sig_of_ind env sigma (ind, u) in
  let indid = ind_name ind in
  let simpl = Tacred.simpl env sigma in
  let poly = Flags.is_universe_polymorphism () in
  let indsig = 
    let indsigid = add_suffix indid "_sig" in
      declare_constant indsigid pred
	None poly sigma (IsDefinition Definition)
  in
  let pack_id = add_suffix indid "_sig_pack" in
  let pack_fn = 
    let vbinder = (Name (add_suffix indid "_var"), None, fullapp) in
    let term = it_mkLambda_or_LetIn valsig (vbinder :: ctx) 
    in
    (* let rettype = mkApp (mkConst indsig, extended_rel_vect (succ lenargs) pars) in *)
      declare_constant pack_id (simpl term)
	None (* (Some (it_mkProd_or_LetIn rettype (vbinder :: ctx))) *)
	poly sigma
	(IsDefinition Definition)
  in
  let sigma = if not poly then Evd.from_env (Global.env ()) else sigma in
  let sigma, c = signature_class sigma in
  let env = Global.env () in
  let sigma, indsig = Evd.fresh_global env sigma (ConstRef indsig) in
  let sigma, pack_fn = Evd.fresh_global env sigma (ConstRef pack_fn) in
  let signature_id = add_suffix indid "_Signature" in
  let inst = 
    declare_instance signature_id
      poly sigma ctx c
      [fullapp; lift lenargs idx;
       mkApp (indsig, extended_rel_vect lenargs pars);
       mkApp (pack_fn, extended_rel_vect 0 ctx)]
  in
  Table.extraction_inline true [Ident (dummy_loc, pack_id)];
  Table.extraction_inline true [Ident (dummy_loc, signature_id)];
  inst

let () =
  let fn env sigma c = ignore (declare_sig_of_ind env sigma c) in
  Derive.(register_derive
            { derive_name = "Signature";
              derive_fn = make_derive_ind fn })

let get_signature env sigma ty =
  try
    let sigma', (idx, _) = 
      new_type_evar env sigma Evd.univ_flexible ~src:(dummy_loc, Evar_kinds.InternalHole) in
    let _idxev = fst (destEvar idx) in
    let sigma', cl = Evarutil.new_global sigma' (Lazy.force signature_ref) in
    let inst = mkApp (cl, [| ty; idx |]) in
    let sigma', tc = Typeclasses.resolve_one_typeclass env sigma' inst in
    let _, u = destInd (fst (destApp inst)) in
    let ssig = mkApp (mkConstG signature_sig u, [| ty; idx; tc |]) in
    let spack = mkApp (mkConstG signature_pack u, [| ty; idx; tc |]) in
      (sigma', nf_evar sigma' ssig, nf_evar sigma' spack)
  with Not_found ->
    let pind, args = Inductive.find_rectype env ty in
    let sigma, pred, pars, _, valsig, ctx, _, _ =
      build_sig_of_ind env sigma pind in
    msg_warning (str "Automatically inlined signature for type " ++
    Printer.pr_pinductive env pind ++ str ". Use [Derive Signature for " ++
    Printer.pr_pinductive env pind ++ str ".] to avoid this.");
    let indsig = pred in
    let vbinder = (Anonymous, None, ty) in
    let pack_fn = it_mkLambda_or_LetIn valsig (vbinder :: ctx) in
    let pack_fn = beta_applist (pack_fn, args) in
      (sigma, nf_evar sigma (mkApp (indsig, Array.of_list args)),
       nf_evar sigma pack_fn)

(* let generalize_sigma env sigma c packid = *)
(*   let ty = Retyping.get_type_of env sigma c in *)
(*   let value, typ = mk_pack env sigma ty in *)
(*   let valsig = value c in *)
(*   let setvar = letin_tac None (Name packid) valsig (Some typ) nowhere in *)
(*   let geneq = generalize [mkCast (mkRefl typ (mkVar packid),  *)
(* 					 DEFAULTcast, mkEq typ (mkVar packid) valsig)] in *)
(*   let clear = clear_body [packid] in *)
(*   let movetop = move_hyp true packid (Tacexpr.MoveToEnd false) in *)
(*     tclTHENLIST [setvar; geneq; clear; movetop] *)

let pattern_sigma ~assoc_right c hyp env sigma =
  let evd = ref sigma in
  let terms = constrs_of_coq_sigma env evd c (mkVar hyp) in
  let terms =
    if assoc_right then terms
    else match terms with
         | (x, t, p, rest) :: term :: _ -> 
	    constrs_of_coq_sigma env evd t p @ terms
         | _ -> terms
  in
  let pat = Patternops.pattern_of_constr env !evd in
  let terms = 
    if assoc_right then terms
    else match terms with
         | (x, t, p, rest) :: _ :: _ -> terms @ constrs_of_coq_sigma env evd t p 
         | _ -> terms
  in
  let projs = map (fun (x, t, p, rest) -> (pat t, make_change_arg p)) terms in
  let projabs =
    tclTHENLIST ((if assoc_right then rev_map
                 else map) (fun (t, p) -> change (Some t) p Locusops.onConcl) projs) in
    Proofview.V82.tactic (tclTHEN (Refiner.tclEVARS !evd) projabs)
			 
let curry_left_hyp env sigma c t =
  let aux c t na u ty pred concl =
    let (n, idx, dom) = destLambda pred in
    let newctx = [(na, None, dom); (n, None, idx)] in
    let tuple = mkApp (mkConstructG coq_sigmaI u,
		       [| lift 2 ty; lift 2 pred; mkRel 2; mkRel 1 |])
    in
    let term = it_mkLambda_or_LetIn (mkApp (lift 2 c, [| tuple |])) newctx in
    let typ = it_mkProd_or_LetIn (subst1 tuple (liftn 2 2 concl)) newctx in
      (term, typ)
  in
  let rec curry_index c t =
    match kind_of_term t with
    | Prod (na, dom, concl) ->
       (match decompose_coq_sigma dom with
	| None -> (c, t)
	| Some (u, ty, pred) ->
	   let term, typ = aux c t na u ty pred concl in
	   match kind_of_term typ with
	   | Prod (na', dom', concl') ->
	      let body' = pi3 (destLambda term) in
	      let c, t = curry_index body' concl' in
	      mkLambda (na', dom', c), mkProd (na', dom', t)
	   | _ -> (term, typ))
    | _ -> (c, t)
  in
  let curry c t =
    match kind_of_term t with
    | Prod (na, dom, concl) ->
       (match decompose_coq_sigma dom with
	| None -> None
	| Some (inst, ty, pred) ->
	   let term, typ = aux c t na inst ty pred concl in
	   let c, t = curry_index term typ in
	     Some (c, t))
    | _ -> None
  in curry c t

let curry na c =
  let rec make_arg na t =
    match decompose_coq_sigma t with
    | None -> 
       if Globnames.is_global (Lazy.force coq_unit) t then
         let _, u = destInd t in
         [], Universes.constr_of_global_univ (Lazy.force coq_tt, u)
       else [na,None,t], mkRel 1
    | Some (u, ty, pred) ->
       let na, _, codom =
         if isLambda pred then destLambda pred 
         else (Anonymous, ty, mkApp (pred, [|mkRel 1|])) in
       let ctx, rest = make_arg na codom in
       let len = List.length ctx in 
       let tuple = 
         mkApp (mkConstructG coq_sigmaI u,
		[| lift (len + 1) ty; lift (len + 1) pred; mkRel (len + 1); rest |])
       in
       ctx @ [na, None, ty], tuple
  in
  make_arg na c

let uncurry_hyps name =
  let open Proofview in
  let open Proofview.Notations in
  Proofview.Goal.enter (fun gl ->
    let hyps = Goal.hyps (Goal.assume gl) in
    let env = Goal.env gl in
    let sigma = Goal.sigma gl in
    let hyps, _ = List.split_when (fun (_, _, ty) -> 
                      Constr.equal ty (Lazy.force coq_end_of_section)) hyps in
    let rec ondecl (sigma, acc, ty) (dna, _, dty) =
      let sigma, sigmaI = Evd.fresh_global env sigma (Lazy.force coq_sigmaI) in
      let _, u = destConstruct sigmaI in
      let types = [| dty; mkNamedLambda dna dty ty |] in
      let app = mkApp (sigmaI, Array.append types [| mkVar dna; acc |]) in
      (sigma, app, mkApp (mkIndG coq_sigma u, types))
    in
    let sigma, unit = Evd.fresh_global env sigma (Lazy.force coq_tt) in
    let sigma, unittype = Evd.fresh_global env sigma (Lazy.force coq_unit) in
    let sigma, term, ty = 
      Context.fold_named_context_reverse 
        ondecl ~init:(sigma, unit, unittype) hyps
    in
    let sigma, _ = Typing.type_of env sigma term in
    Proofview.Unsafe.tclEVARS sigma <*>
      Tactics.letin_tac None (Name name) term (Some ty) nowhere)

let uncurry_call env sigma c =
  let hd, args = decompose_app c in
  let ty = Retyping.get_type_of env sigma hd in
  let ctx, concl = decompose_prod_n_assum (List.length args) ty in
  let evdref = ref sigma in
  (* let ctx = (Anonymous, None, concl) :: ctx in *)
  let sigty, sigctx, constr = telescope evdref ctx in
  let app = substl (List.rev args) constr in
  !evdref, app, sigty

(* Generalization of a term. *)

let build_generalization_ref = lazy (init_reference
  ["Equations";"Generalization"] "Build_Generalization")
let build_generalization_constr evd =
  Evarutil.e_new_global evd (Lazy.force build_generalization_ref)

(* Produce parts of a case on a variable, while introducing cuts and
 * equalities when necessary.
 * This function requires a full rel_context, a rel to eliminate, and a goal.
 * It returns a return type for the case, and a list of contr that need to
 * be applied to the case for it to be valid. *)
let smart_case (env : Environ.env) (evd : Evd.evar_map ref)
  (ctx : Context.rel_context) (rel : int) (goal : Term.types) :
    Term.types * Term.constr list =
  let after, (_, _, rel_ty), before = Covering.split_context (pred rel) ctx in
  let rel_ty = Vars.lift rel rel_ty in
  let rel_t = Constr.mkRel rel in
  (* Fetch some information about the type of the variable being eliminated. *)
  let pind, args = Inductive.find_inductive env rel_ty in
  let mib, oib = Global.lookup_pinductive pind in
  let params, indices = List.chop mib.mind_nparams args in
  let indfam = Inductiveops.make_ind_family (pind, params) in
  let arity_ctx, ind_decl =
    match Inductiveops.make_arity_signature env true indfam with
    | ind_decl :: ctx -> ctx, ind_decl
    | _ -> assert false
  in
  let rev_arity_ctx = List.rev arity_ctx in
  (* Firstly, we need to analyze each index to decide if we should introduce
   * an equality for it or not. *)
  (* For each index of the type, we _omit_ it if and only if
   *   1) It is a variable.
   *   2) It did not appear before.
   *   3) Its type does not depend on something that was not omitted before.
  *)
  let rec compute_omitted prev_indices indices prev_ctx ctx omitted nb =
    match indices, ctx with
    | [], [] -> omitted, nb, prev_indices
    | idx :: indices, decl :: ctx ->
        let omit =
          (* Variable. *)
          if not (Term.isRel idx) then false
          (* Linearity. *)
          else if List.exists (Term.eq_constr idx) params then false
          else if List.exists (Term.eq_constr idx) prev_indices then false
          (* Dependency. *)
          else
            let _, _, decl_ty = decl in
            let deps = Termops.free_rels decl_ty in
              Int.Set.fold (fun x b ->
                b && try Option.has_some (List.nth omitted (x-1))
                with Failure _ | Invalid_argument _ -> true) deps true
        in
        compute_omitted (idx :: prev_indices) indices
                        (decl :: prev_ctx) ctx
                        ((if omit then Some (Term.destRel idx) else None) :: omitted)
                        (if omit then nb else succ nb)
    | _, _ -> assert false
  in
  let omitted, nb, rev_indices =
    compute_omitted [] indices [] rev_arity_ctx [] 0 in
  (* Do we need to omit the variable itself? *)
  let omit_variable =
    let dep_var = CList.fold_left_i (fun i dep (_, b, t) -> dep ||
        let is_dep t = not (Vars.noccurn (rel - i) t) in
        Option.cata is_dep false b || is_dep t
      ) 1 (not (Vars.noccurn rel goal)) after
    in
    if Int.equal nb 0 || not dep_var then
      Some rel
    else
      None
  in
  let omitted = omit_variable :: omitted in
  let rev_indices = rel_t :: rev_indices in
  let return_ctx = ind_decl :: arity_ctx in
  let nb = if Option.has_some omit_variable then nb else succ nb in
  (* From this data, we can prepare a function that performs the substitution
   * between the omitted variables and their corresponding variables in the
   * context. This function takes a constr typed under the context
   * [arity_ctx @ ctx] and returns a constr typed under the same
   * context, where every variable in [omitted] has been replaced by its
   * corresponding index. *)
  let subst_omitted (c : constr) =
    CList.fold_left_i (fun i c -> function
      | Some x ->
          (* [x] was computed under the context [ctx], we need to lift it. *)
          Termops.replace_term (Constr.mkRel (x + oib.mind_nrealargs + 1))
            (Constr.mkRel i) c
      | None -> c
    ) 1 c omitted
  in
  (* At this point, we are ready to produce an equality between telescopes,
   * if needed. First, we can eliminate the trivial case where everything was
   * omitted. *)
  if Int.equal nb 0 then
    let goal = Vars.lift (succ oib.mind_nrealargs) goal in
    let goal = subst_omitted goal in
    let case_ty = Termops.it_mkLambda_or_LetIn goal return_ctx in
      case_ty, []
  else
    (* Otherwise, we need to build a context that we can use with [telescope].
     * This context will be valid under [ctx]. *)
    (* (Recall that a telescope is a reversed context. *)
    let _, rev_sigctx, tele_lhs, tele_rhs =
      CList.fold_left3 (fun (k, rev_sigctx, tele_lhs, tele_rhs) omit decl idx ->
        match omit with
        | Some x ->
          (* Don't add a binder for this index, since it is omitted. *)
          (* We need, however, to substitude [Rel 1] by the corresponding
           * omitted rel for the telescope to be valid. *)
          (* [x] is valid under [ctx], and [k] is the number of binders above
           * the current declaration. *)
          let rev_sigctx = Covering.subst_telescope (Constr.mkRel (x + k))
            rev_sigctx in
          pred k, rev_sigctx, tele_lhs, tele_rhs
        | None ->
          (* Add a binder to the telescope. *)
          let rhs = Constr.mkRel (succ oib.mind_nrealargs - k) in
          pred k, decl :: rev_sigctx, idx :: tele_lhs, rhs :: tele_rhs
      ) (oib.mind_nrealargs, [], [], []) omitted return_ctx rev_indices
    in
    let sigctx = List.rev rev_sigctx in
    let sigty, _, sigconstr = telescope evd sigctx in
    (* [sigconstr] is a telescope ready to contain the indices that we need. *)
    (* We will produce an equality between two telescopes, one with indices
     * from the new [arity_ctx], and one with indices from the variable. *)
    let left_sig = Vars.substl (List.rev tele_lhs) sigconstr in
    (* [left_sig] is valid under [ctx] as was [true_indices], let's lift it. *)
    let lifted_left_sig = Vars.lift (succ oib.mind_nrealargs) left_sig in
    (* The same holds for [sigty]. *)
    let lifted_sigty = Vars.lift (succ oib.mind_nrealargs) sigty in
    (* For the right-hand-side, we have to replace [Rel 1; ..; Rel nb] by
     * some subset of [Rel 1; ..; Rel (succ oib.mind_nparams)]. *)
    let lifted_sigconstr = Vars.liftn (succ oib.mind_nrealargs) (succ nb) sigconstr in
    let right_sig = Vars.substl (List.rev tele_rhs) lifted_sigconstr in
    let eq = Equations_common.mkEq evd lifted_sigty lifted_left_sig right_sig in
    (* At this point, [eq] is an equality valid under [arity_ctx @ ctx], with
     * a right-hand-side which is only rels, and left-hand-side which contains
     * the indices of the variable being eliminated, lifted accordingly so
     * that none of them refer to [arity_ctx]. *)
    let goal = Vars.lift (oib.mind_nrealargs + 2) goal in
    let goal = Term.mkProd (Anonymous, eq, goal) in
    (* We can start filling the terms we will need to apply to the case. *)
    let to_apply = [Equations_common.mkRefl evd sigty left_sig] in
    (* Now we need to care about cuts if we need them. *)
    (* For every variable in the context, we check if these conditions hold:
     *   i) Its type depends on a variable that was omitted or cut.
     *   ii) It is not omitted itself.
     * If that is the case, we need to introduce a cut. *)
    (* To help a little bit, we compute a set of omitted rels. *)
    let omitted_rels = List.fold_left (fun omitted_rels omit ->
      Option.fold_right Int.Set.add omit omitted_rels) Int.Set.empty omitted in
    let lenctx = List.length ctx in
    let cut_ctx, _, _ = List.fold_right_i (fun k (name, body, decl_ty)
      (cut_ctx, cut_rels, managed) ->
      let rel = lenctx - k in
      let cut =
        if Int.Set.mem rel omitted_rels then false
        else
          let rels = Termops.free_rels decl_ty in
            Int.Set.exists (fun i -> let rel' = i + rel in
              Int.Set.mem rel' omitted_rels || Int.Set.mem rel' cut_rels) rels
      in
      if not cut then (cut_ctx, cut_rels, false :: managed)
      else
        (* We want to insert a cut for this variable. *)
        let decl_ty = Vars.lift (rel + oib.mind_nrealargs + 1) decl_ty in
        let decl_ty, _ = List.fold_left_i (fun i (decl_ty, j) managed ->
          if managed then
            let decl_ty = Vars.lif 1 decl_ty in
              Termops.replace_term (Constr.mkRel (rel + i))
        ) 0 (decl_ty, 1)
        assert false
    ) 0 ctx ([], Int.Set.empty, []) in

    (* All the cuts have been inserted, and [to_apply] has been updated
     * accordingly, we can now substitute the omitted variables for their
     * correct rel, and wrap everything under lambdas. *)
    let goal = subst_omitted goal in
    let case_ty = Termops.it_mkLambda_or_LetIn goal return_ctx in
      case_ty, to_apply

(* It is assumed that we want to build a term of type [@Generalization ty c],
 * and that [ty] and [c] are typed under the named_context of env. *)
let generalization (env : Environ.env) (ty : Term.types) (c : Term.constr)
  (sigma : Evd.evar_map) : Evd.evar_map * Term.constr =
  let evd = ref sigma in
  let pind, args = Inductive.find_inductive env ty in
  (* Identifiants already in the context. *)
  let ids = Termops.ids_of_context env in

  (* A predicate identifier. *)
  let pred_id = Namegen.next_ident_away_in_goal (Names.id_of_string "P") ids in
  (* A type for the predicate. *)
  let pred_ty = Evarutil.e_new_Type env evd in

  (* Build the type of the generalized proof. *)
  (* First, get the arity of the inductive family. *)
  let mib, oib = Global.lookup_pinductive pind in
  let params, indices = List.chop mib.mind_nparams_rec args in
  let indf = Inductiveops.make_ind_family (pind, params) in
  let arity = Inductiveops.make_arity_signature env true indf in
  (* Then, get the signature of this inductive family under this arity. *)
  let _, _, _, _, _, _, right_valsig, tysig =
    let pars = Inductiveops.inductive_paramdecls pind in
    let parapp = Term.applist (Constr.mkIndU pind, params) in
      sigmaize env evd pars parapp in
  (* Generate the signature corresponding to the original term. *)
  (* Nota: we should normally lift the indices, but we supposed they did
   * not contain any rel. *)
  let left_valsig = Vars.substl (c :: List.rev indices) right_valsig in
  (* Build the equality between the two signatures. *)
  let eq = Equations_common.mkEq evd tysig left_valsig right_valsig in
  (* Build the goal under the arity and equality. *)
  let goal = Constr.mkRel (oib.mind_nrealargs + 3) in
  (* Finally build the goal after generalization. *)
  let generalized_goal =
    Term.it_mkProd_or_LetIn goal ((Anonymous, None, eq) :: arity) in
  (* The final type. *)
  let gen_id = Namegen.next_ident_away_in_goal (Names.id_of_string "H") ids in
  let generalization_ty = Constr.mkProd (Names.Name.Name gen_id, generalized_goal, Constr.mkRel 2) in
  let generalization_ty = Constr.mkLambda (Names.Name.Name pred_id, pred_ty, generalization_ty) in
  (*
  let generalization_ty = Term.it_mkProd_or_LetIn (Constr.mkRel 2) ctx in
  *)
  (* Build the corresponding proof. *)
  let proof = Term.applist (Constr.mkRel 1, indices) in
  let refl = Equations_common.mkRefl evd tysig left_valsig in
  let proof = Constr.mkApp (proof, [| c; refl |]) in
  let ctx =
    [(Names.Name.Name gen_id, None, generalized_goal); (Names.Name.Name pred_id, None, pred_ty)] in
  let generalization = Term.it_mkLambda_or_LetIn proof ctx in

  (* Build the instance itself. *)
  let build_gen = build_generalization_constr evd in
  let instance = Constr.mkApp (build_gen, [| ty; c; generalization_ty; generalization |]) in
    !evd, instance

