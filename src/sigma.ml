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

(* Generalize a term while taking care of which variables we actually need
 * to generalize, with the goal of eliminating the variable. This function
 * requires a full rel_context, a rel to generalize, and a goal. It returns
 * the type after generalization, the proof term that witnesses it, the 
 * context of the generalization (i.e., the fresh variables added in the
 * context), its length, and a
 * list of [int option] keeping track of the indices that have been
 * omitted from the generated fresh variables. All these indices are
 * necessarily rels. *)
let smart_generalization (env : Environ.env) (evd : Evd.evar_map ref)
  (ctx : Context.rel_context) (rel : int) (goal : Term.types) :
    Term.types * Term.constr * Context.rel_context * int * int option list =
  let after, (_, _, rel_ty), before = Covering.split_context (pred rel) ctx in
  let rel_ty = Vars.lift rel rel_ty in
  let rel_t = Constr.mkRel rel in
  (* For this, we need to analyze the variable and each of its indices,
   * to generate fresh names only for those that need them. *)
  (* For each index of the type, we omit it only if
     1) It is a variable.
     2) It did not appear before.
     3) Its type does not depend on something that was not omitted before. *)
  (* For this analysis, we will need the arity of the inductive type,
   * as it is the reference for the criterion 3). *)
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

  (* As a first step, we compute a simple list of booleans, to know if
     an index is omitted or not. *)
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
            (* TODO *)
            false 
        in
        compute_omitted (idx :: prev_indices) indices
                        (decl :: prev_ctx) ctx
                        ((if omit then Some (Term.destRel idx) else None) :: omitted)
                        (if omit then nb else succ nb)
    | _, _ -> assert false
  in
  let omitted, nb, rev_indices =
    compute_omitted [] indices [] rev_arity_ctx [] 0 in
  (* TODO Here we can add the variable itself to [omitted] and [rev_indices]. *)
  (*
  let omitted = Some rel :: omitted in
  let rev_indices = rel_t :: rev_indices in
  let arity_ctx = ind_decl :: arity_ctx in
  *)
  let omitted = None :: omitted in
  let rev_indices = rel_t :: rev_indices in
  let arity_ctx = ind_decl :: arity_ctx in
  let nb = succ nb in
  (* Shortcut in case we omit everything. *)
  if Int.equal nb 0 then
    goal, Constr.mkLambda (Anonymous, goal, Constr.mkRel 1), [], 0, omitted
  else begin
    (* Now we build a context that we can use with [telescope]. *)
    let _, rev_sigctx, true_indices =
      CList.fold_left3 (fun (k, ctx, true_indices) omit decl idx ->
      if Option.has_some omit then
        let idx = Vars.lift k idx in
        (* Don't add a binder, but substitute [idx] for [Rel 1]. *)
        (* Also, be careful that [idx] is typed under the "toplevel"
         * context, while [ctx] is typed under the remaining [arity_ctx]. *)
        pred k, Covering.subst_rel_context 1 idx ctx, true_indices
      else
        (* Add a binder to the context. *)
        pred k, decl :: ctx, idx :: true_indices
    ) (pred oib.mind_nrealargs, [], []) omitted arity_ctx rev_indices in
    let sigctx = List.rev rev_sigctx in
    let sigty, _, sigconstr = telescope evd sigctx in
    (* At this point, sigconstr is a telescope ready to contain the
     * indices of the old and fresh variables. *)
    
    (* Produce an equality type under the context [sigctx ++ ctx]. *)
    (* [sigconstr] contains rels for each index that was not omitted. *)
    let left_sig = Vars.substl (List.rev true_indices) sigconstr in
    let lifted_left_sig = Vars.lift nb left_sig in
    let lifted_sigty = Vars.lift nb sigty in
    let eq = Equations_common.mkEq evd lifted_sigty lifted_left_sig sigconstr in

    (* [gen_ty] is a valid type under [ctx] and is the goal after
     * generalization. *)
    let gen_ty = Term.it_mkProd_or_LetIn (Vars.lift (succ nb) goal)
      ((Anonymous, None, eq) :: sigctx) in
    (* [gen_proof] is the corresponding proof, also under [ctx]. *)
    (* It has type [(gen_ty -> goal) -> goal]. *)
    let true_indices = List.map (Vars.lift 1) true_indices in
    let proof = Term.applist (Constr.mkRel 1, true_indices) in
    let refl = Equations_common.mkRefl evd sigty left_sig in
    let proof = Constr.mkApp (proof, [| Vars.lift 1 refl |]) in
    let gen_proof = Constr.mkLambda (Anonymous, gen_ty, proof) in
      gen_ty, gen_proof, sigctx, nb, omitted
  end

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

