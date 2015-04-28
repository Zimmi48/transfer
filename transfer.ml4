(* Apply a theorem modulo isomorphism *)
(*   Copyright Théo Zimmermann 2015   *)

DECLARE PLUGIN "transfer"

open Names
open Term
open Vars
open Proofview
open Clenv
open Coqlib
open Constrexpr
open Globnames
open Printer
open Pp
open Mod_subst
open Libobject
open Lib

type ('a, 'b) either = Left of 'a | Right of 'b
       
module PairConstr =
  struct
    type t = constr * constr
    let compare (x1, x2) (y1, y2) =
      match Constr.compare x1 y1 with (* compare is defined on constr *)
      | 0 -> compare x2 y2
      | x -> x
	       (* or should we rather test for conversion?*)
  end
    
module PMap = Map.Make(PairConstr)
(* This extra step is needed so that empty has not a polymorphic type
 * and can be used inside a Map *)
let emptys : (constr * constr * constr) PMap.t = PMap.empty
let emptyt : (constr * constr) PMap.t = PMap.empty

let surjections = ref emptys
let transfers = ref emptyt

let freeze _ = (!surjections, !transfers)
		  
let unfreeze (surj, transf) =
  surjections := surj;
  transfers := transf
		 
let init () =
  surjections := emptys;
  transfers := emptyt
		    
let _ =
  Summary.declare_summary "transfer"
    { Summary.freeze_function = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = init }

let load_surjection _ _ = ()
let open_surjection i (_, (k, c)) =
  if i = 1 then
    surjections := PMap.add k c !surjections
let cache_surjection o =
  load_surjection 1 o;
  open_surjection 1 o
let subst_surjection (subst , ((k1, k2), (c1, c2, c3))) =
  ((subst_mps subst k1, subst_mps subst k2),
   (subst_mps subst c1, subst_mps subst c2, subst_mps subst c3))
let classify_surjection x = Substitute x
let discharge_surjection _ = None (* TODO *)
      
let inSurjection : PMap.key * (constr * constr * constr) -> obj =
  declare_object {(default_object "SURJECTION") with
    open_function = open_surjection;
    load_function = load_surjection;
    cache_function = cache_surjection;
    subst_function = subst_surjection;
    classify_function = classify_surjection;
    discharge_function = discharge_surjection }
    
let load_transfer _ _ = ()
let open_transfer i (_, (k, c)) =
  if i = 1 then
    transfers := PMap.add k c !transfers
let cache_transfer o =
  load_transfer 1 o;
  open_transfer 1 o
let subst_transfer (subst , ((k1, k2), (c1, c2))) =
  ((subst_mps subst k1, subst_mps subst k2),
   (subst_mps subst c1, subst_mps subst c2))
let classify_transfer x = Substitute x
let discharge_transfer _ = None (* TODO *)
      
let inTransfer : PMap.key * (constr * constr) -> obj =
  declare_object {(default_object "TRANSFER") with
    open_function = open_transfer;
    load_function = load_transfer;
    cache_function = cache_transfer;
    subst_function = subst_transfer;
    classify_function = classify_transfer;
    discharge_function = discharge_transfer }

let constr_and_type_of_ref r =
  let t = Constrintern.intern_reference r in
  let constr = Universes.constr_of_global t in
  let typ = fst (Universes.type_of_global t) in (* unsafe *)
  constr, typ
	    
let string_of_name = function
  | Name id -> string_of_id id
  | _ -> "?"
			     
(* Do not forget to handle backtracking *)
let add_surjection f g proof =
  let env = Global.env () in
  let proofterm , thm = constr_and_type_of_ref proof in
  let f_fun , f_typ = constr_and_type_of_ref f in
  let g_fun , g_typ = constr_and_type_of_ref g in
  let key =
    match kind_of_term f_typ, kind_of_term g_typ, kind_of_term thm with
    | Prod (_, t1, t2), Prod(_, t3, t4), Prod(id_or_anon, t5, t6) ->
       let name = string_of_name id_or_anon in
       begin try
	   Reduction.conv env t1 t4; (* modulo conversion *)
	   Reduction.conv env t2 t3;
	   Reduction.conv env t2 t5;
	   let new_env = Environ.push_rel (id_or_anon,None,t5) env in
	   let hd , args = decompose_app t6 in
	   if not (is_global (build_coq_eq ()) hd) then
	     Errors.errorlabstrm "" (str "In the statement of " ++ pr_lconstr proofterm ++ str ", " ++ pr_lconstr_env new_env Evd.empty t6 ++ str " is not an equality.");
	   begin match args with
		 | [ _ ; fgx ; x ] when isRelN 1 x ->
		    begin match kind_of_term fgx with
			  | App (f , [| gx |]) ->
			     Reduction.conv env f f_fun;
			     begin match kind_of_term gx with
				   | App (g , [| x |]) when isRelN 1 x ->
				      Reduction.conv env g g_fun
				   | _ -> Errors.errorlabstrm "" (str "In the statement of " ++ pr_lconstr proofterm ++ str ", cannot unify " ++ pifb () ++ pr_lconstr_env new_env Evd.empty gx ++ str " and " ++ pr_lconstr_env new_env Evd.empty (mkApp (g_fun, [| mkRel 1 |])) ++ str ".")
			     end
			  | _ -> Errors.errorlabstrm "" (str "In the statement of " ++ pr_lconstr proofterm ++ str ", the left-hand side of the equality should be " ++ pifb () ++ pr_lconstr_env new_env Evd.empty (mkApp (f_fun, [| (mkApp (g_fun, [| mkRel 1 |])) |])) ++ str " instead of " ++ pr_lconstr_env new_env Evd.empty fgx ++ str ".")
		    end
		 | _ -> Errors.errorlabstrm "" (str "In the statement of " ++ pr_lconstr proofterm ++ str (", the right-hand side of the equality should be " ^ name ^ "."))
	   end;
	 with Reduction.NotConvertible -> Errors.error "Types of functions and/or statement of theorem are incompatible."
       end;
       t1 , t2
    | _ -> Errors.error "Some arguments have a wrong type."
  in
  add_anonymous_leaf (inSurjection (key, (f_fun, g_fun, proofterm)))
			  
let add_transfer f r r' proof =
  let env = Global.env () in
  let proofterm , thm = constr_and_type_of_ref proof in
  let f_fun , f_typ = constr_and_type_of_ref f in
  let r_rel , r_typ = constr_and_type_of_ref r in
  let r'_rel , r'_typ = constr_and_type_of_ref r' in
  let _ = match kind_of_term f_typ with
    | Prod (_, t1, t2) ->
       let rec check r r' thm args =
	 match kind_of_term r, kind_of_term r', kind_of_term thm with
	 (* the relation takes more arguments *)
	 (* for the moment we assume that all arguments are of respective
            types t1 and t2. A more general form would be to allow any other
            type provided that t3 = t5 = t7. *)
	 | Prod (_, t3, t4), Prod(_, t5, t6), Prod(name, t7, t8) ->
	    begin try
		Reduction.conv env t1 t3;
		Reduction.conv env t2 t5;
		Reduction.conv env t3 t7;
		check t4 t6 t8 (string_of_name name :: args)
	      with Reduction.NotConvertible -> Errors.error "Types of functions and/or statement of theorem are incompatible."
	    end
	 (* the relation has no more arguments *)
	 | Sort _ , Sort _ , Prod(_, hyp, concl) ->
	    begin match kind_of_term hyp, kind_of_term concl with
		  | App (r , r_args) , App (r' , r'_args) ->
		     begin try
			 Reduction.conv env r r_rel;
			 Reduction.conv env r' r'_rel;
			 (* by type-checking we are sure that args, r_args and
                            r'_args have the same length *)
			 (* 1. check that the hypothesis has the right form *)
			 let n = Array.length r_args in
			 for i = 0 to n - 1 do
			   if not (isRelN (n - i) r_args.(i)) then
			     Errors.error ("In hypothesis, argument " ^ string_of_int (i + 1) ^ " should be " ^ (List.nth args (n - i - 1)) ^ ".")
			 done;
			 (* 2. check that the conclusion has the right form *)
			 for i = 0 to n - 1 do
			   try match kind_of_term r'_args.(i) with
			       | App (f , [| x |]) when isRelN (n - i + 1) x ->
				  (* de Bruijn indices are shifted because of
                                     the hypothesis *)
				  Reduction.conv env f_fun f
			       | _ -> raise Reduction.NotConvertible
			   with Reduction.NotConvertible -> Errors.errorlabstrm "" (str "In conclusion " ++ pr_lconstr concl ++ str (", argument " ^ string_of_int (i + 1) ^ " should be ") ++ pr_lconstr f_fun ++ str ((List.nth args (n - i - 1)) ^ "."))
			 done			 
		       with Reduction.NotConvertible -> Errors.error "The hypothesis and conclusion should be formed of the appropriate relation applied to arguments."
		     end
		  | _ -> Errors.error "The theorem has a wrong form."
	    end
	 | _ -> Errors.error "Some arguments have a wrong type."
       in
       check r_typ r'_typ thm []
    | _ -> Errors.errorlabstrm "" (pr_lconstr f_fun ++ str " has not a function type.")
  in
  let key = (r_rel, r'_rel) in
  add_anonymous_leaf (inTransfer (key, (f_fun, proofterm)))

let rec splitReln covariant n t = match kind_of_term t with
  | Rel k when k < n -> mkRel k
  | Rel k when covariant && n = k -> mkRel n
  | Rel k -> mkRel (k + 1)
  | Prod(name, t1, t2) ->
     mkProd(name,
	    splitReln (not covariant) n t1,
	    splitReln covariant (n + 1) t2)
  | _ -> Constr.map_with_binders succ (splitReln covariant) n t
    
(* given types thm and concl, exact_modulo tries to automatically prove
   thm -> concl by using transfer and surjection lemmas previously declared *)
let rec exact_modulo env sigma thm concl proofthm
	: Evd.evar_map * Constr.t =
  let thm = Reductionops.whd_betaiotazeta sigma thm in
  let concl = Reductionops.whd_betaiotazeta sigma concl in
  match kind_of_term thm, kind_of_term concl with

  | App (f1 , l1) , App (f2 , l2) ->
     let n = Array.length l1 in
     let m = Array.length l2 in
     if n <> m then
       Errors.error (* f1 and f2 have *) "Not the same number of arguments.";
     (* try exact match first *)
     let sigma', return = Reductionops.infer_conv env sigma f1 f2 in
     if return then
       (* When we start accepting functions and not just relations,
          we should recurse in the arguments. *)
       let i = ref 0 in
       let sigma_return = ref (sigma', true) in
       while snd (!sigma_return) && !i < n do
	 sigma_return :=
	   Reductionops.infer_conv env (fst (!sigma_return)) l1.(!i) l2.(!i);
	 incr i
       done;
       if !i = n then
	 fst (!sigma_return), proofthm
       else
	 Errors.errorlabstrm "" (str "Cannot unify " ++ quote (pr_lconstr_env env (fst (!sigma_return)) l1.(!i - 1)) ++ str " and " ++ quote (pr_lconstr_env env (fst (!sigma_return)) l2.(!i - 1)) ++ str ".")
     else (* there may be a transfer required *)
       let (surj, proofsurj) = try PMap.find (f1, f2) !transfers
			   with Not_found ->
			     (* if const recurse after one step of delta *)
			     Errors.errorlabstrm "" (str "Cannot unify " ++ pr_lconstr f1 ++ str " and " ++ pr_lconstr f2 ++ str " (no adequate transfer declared).") in
       (* for now, PMap.find is based on Constr.equal but if we decide to look
          in the table modulo unification, then we will have to get back a
          sigma *)
       let i = ref 0 in
       let sigma_return = ref (sigma, true) in
       while snd (!sigma_return) && !i < n do
	 sigma_return := Reductionops.infer_conv env
						 (fst (!sigma_return))
						 (mkApp (surj , [| l1.(!i) |]))
						 l2.(!i);
	 incr i
       done;
       if !i = n then
	 fst (!sigma_return),
	 mkApp (mkApp (proofsurj, l1) , [| proofthm |])
       else
	 Errors.errorlabstrm "" (str "Cannot unify " ++ pifb () ++ pr_lconstr_env env (fst (!sigma_return)) (mkApp (surj , [| l1.(!i - 1) |])) ++ str " and " ++ pr_lconstr_env env (fst (!sigma_return)) l2.(!i - 1) ++ str ".")

  | Prod (_, t1, t2) , Prod (name, t3, t4) ->
     let sigma, unifproof =
       try
	 let sigma, unifproof =
	   exact_modulo env sigma t3 t1 (mkRel 1) in
	 sigma, Left unifproof
       with Errors.UserError (e, e') ->
	 (* at that point we may want to save that error message *)
	 sigma, Right (e, e')
     in
     let env = Environ.push_rel (name, None, t3) env in
     begin match unifproof with
	   | Left unifproof -> (* if t1 = t3 *)
	      let sigma, p_rec = exact_modulo
				   env sigma t2 t4
				   (mkApp (lift 1 proofthm, [| unifproof |])) in
	      sigma,
	      mkLambda (name, t3, p_rec)
	   | Right (e, e') -> (* there may be a transfer required *)
	      let (surj, inv, prooftransf) = try PMap.find (t1, t3) !surjections
					     with Not_found ->
					       raise (Errors.UserError (e, e'))
	      in
	      (* for now, PMap.find is based on Constr.equal but if we decide
                 to look in the table modulo unification, then we will have to
                 get back a sigma *)
	      let sigma, p_rec =
		exact_modulo
		  env sigma
		  (subst1 (mkApp (inv, [| mkRel 1 |])) (liftn 1 2 t2))
		  (* substitute all occurrences of x with (inv x) *)
		  (subst1 (mkApp (surj, [| (mkApp (inv, [| mkRel 1 |])) |]))
			 (splitReln true 1 t4))
		  (* substitute some occurrences of x with (surj (inv x)) *)
		  (mkApp (lift 1 proofthm, [| mkApp (inv, [| mkRel 1 |]) |]))
	      in
	      sigma,
	      mkLambda (name, t3,
			mkApp (
			    (* eq_rect *)
			    Universes.constr_of_global
			      (Indrec.lookup_eliminator
				 (fst
				    (destInd
				       (Universes.constr_of_global
					  (build_coq_eq ()))))
				 InType),
			    
			    [| lift 1 t3 ;
			       mkApp (surj,
				      [| (mkApp (inv, [| mkRel 1 |])) |]) ;
			       (mkLambda (* why this lift? *)
				  (name, lift 1 t3, splitReln true 1 t4)) ;
			       p_rec ;
			       mkRel 1 ;
			       mkApp (prooftransf , [| mkRel 1 |]) |]))
     end
  | _ ->
     let sigma, return = Reductionops.infer_conv env sigma thm concl in
     if return then
       sigma, proofthm
     else
       Errors.errorlabstrm "" (str "Cannot unify " ++ quote (pr_lconstr_env env Evd.empty thm) ++ str " and " ++ quote (pr_lconstr_env env Evd.empty concl) ++ str ".")

let exact_modulo_tactic (_, proof) = (* Of what use is this evd _? *)
  Goal.nf_enter (* enter wouldn't work : Goal.concl goal wouldn't type check *)
    begin fun goal ->
	  let env = Goal.env goal in
	  let concl = Goal.concl goal in
	  Refine.refine (fun sigma ->
			 let thm = Retyping.get_type_of env sigma proof in
			 exact_modulo env sigma thm concl proof
			)
    end
    
VERNAC COMMAND EXTEND DeclareSurjection
| [ "Declare" "Surjection" reference(f)
	      "by" "(" reference(g) "," reference(proof) ")" ]
  -> [ add_surjection f g proof ]
END

VERNAC COMMAND EXTEND DeclareTransfer
| [ "Declare" "Transfer" reference(r) "to" reference(r')
	      "by" "(" reference(f) "," reference(proof) ")" ]
  -> [ add_transfer f r r' proof ]
END       

TACTIC EXTEND exact_modulo
| [ "exact" "modulo" open_constr(c) ]
  -> [ exact_modulo_tactic c ]
END
