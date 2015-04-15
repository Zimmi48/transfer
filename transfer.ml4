(* Apply a theorem modulo isomorphism *)
(*   Copyright Théo Zimmermann 2015   *)

(* How to use (with Coq 8.5 trunk):
 * $ coq_makefile transfer.ml4 -o Makefile
 * $ make
 * $ coqtop -load-ml-object transfer.cmxs
 * Coq < Declare ML Module "t".
 *)

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
  surjections := PMap.add key
                          (f_fun, g_fun, proofterm)
                          !surjections
			  
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
  transfers := PMap.add key (f_fun, proofterm) !transfers

(* given types thm and concl, exact_modulo tries to automatically prove
   thm -> concl by using transfer and surjection lemmas previously declared *)
let rec exact_modulo env sigma thm concl : Evd.evar_map * Constr.t =
  match kind_of_term (Reductionops.whd_betaiotazeta sigma thm) ,
	kind_of_term (Reductionops.whd_betaiotazeta sigma concl) with

  | App (f1 , l1) , App (f2 , l2) ->
     (* try exact match first *)
     let sigma', return = Reductionops.infer_conv env sigma f1 f2 in
     if return then
       (* When we start accepting functions and not just relations,
          we should recurse in the arguments. *)
       let n = Array.length l1 in
       let m = Array.length l2 in
       if n <> m then Errors.error (* f1 and f2 have *) "Not the same number of arguments.";
       let i = ref 0 in
       let sigma_return = ref (sigma', true) in
       while snd (!sigma_return) && !i < n do
	 sigma_return :=
	   Reductionops.infer_conv env (fst (!sigma_return)) l1.(!i) l2.(!i);
	 incr i
       done;
       if !i = n then
	 fst (!sigma_return), mkLambda (Anonymous, thm, mkRel 1)
       else
	 Errors.error ("Cannot unify the arguments in position " ^ string_of_int !i ^ ".") (* of f1 and f2 *)
     else (* there may be a transfer required *)
       let (surj, proof) = try PMap.find (f1, f2) !transfers
			   with Not_found ->
			     (* if const recurse after one step of delta *)
			     Errors.errorlabstrm "" (str "Cannot unify " ++ pr_lconstr f1 ++ str " and " ++ pr_lconstr f2 ++ str "(no adequate transfer declared).") in
       (* for now, PMap.find is based on Constr.equal but if we decide to look
          in the table modulo unification, then we will have to get back a
          sigma *)
       let n = Array.length l1 in
       let m = Array.length l2 in
       if n <> m then Errors.error (* f1 and f2 have *) "Not the same number of arguments.";
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
	 mkLambda(Anonymous, thm, mkApp (mkApp (proof, l1) , [| mkRel 1 |]))
       else
	 Errors.errorlabstrm "" (str "Cannot unify " ++ pifb () ++ pr_lconstr_env env (fst (!sigma_return)) (mkApp (surj , [| l1.(!i - 1) |])) ++ str " and " ++ pr_lconstr_env env (fst (!sigma_return)) l2.(!i - 1) ++ str ".")

  | Prod (_, t1, t2) , Prod (name, t3, t4) ->
     (* unifproof has type t3 -> t1 *)
     (* we use eq_ind but we should use eq_rect? *)
     (* p_rec will have type t2' -> t4'
        and adapt p_rec will have type t2 -> t4 *)
     let (sigma, unifproof), t2', t4', adapt =
       try exact_modulo env sigma t3 t1, t2, t4, fun x -> x
       with
	 Errors.UserError _ as x -> (* there may be a transfer required *)
	 let (surj, inv, surjproof) = try PMap.find (t1, t3) !surjections
				  with Not_found -> raise x in
	 (* for now, PMap.find is based on Constr.equal but if we decide to look
            in the table modulo unification, then we will have to get back a
            sigma *)
	 let unifproof = mkLambda(Anonymous, t3, mkApp (inv, [| mkRel 1 |])) in
	 (* t2', t4' and adapt p_rec are defined in a new_env context
            with mkRel 1 = x of type t3 *)
	 let t2' = subst1 (mkApp (inv, [| mkRel 1 |])) t2 in
	 (* substitute all occurrences of x with (inv x) *)
	 let t4' = subst1 (mkApp (surj, [| (mkApp (inv, [| mkRel 1 |])) |])) t4
	 in (* substitutes all occurrences of x with (surj (inv x)) *)
	 let adapt p_rec =
	   mkLambda (Anonymous, t2', mkApp (p_rec , [| mkRel 1 |] ))
	 (*
	   mkLambda (Anonymous, t2,
		     mkApp
		       (* eq_rect *)
		       (Universes.constr_of_global
			  (Indrec.lookup_eliminator
			     (fst
				(destInd
				   (Universes.constr_of_global
				      (build_coq_eq ())
				   )
				)
			     ) InType),
			[| t3 ;
			   mkApp (surj, [| (mkApp (inv, [| mkRel 2 |])) |]) ;
			   mkLambda (name, t3, t4) ;
			   mkApp
			     (p_rec,
			      [| mkApp (mkRel 1,
					[| mkApp (inv, [| mkRel 2 |]) |]) |]) ;
			   mkRel 2 ; (* this is x *)
			   mkApp (surjproof , [| mkRel 2 |]) |])
		    ) *) in
	 (sigma, unifproof), t2', t4', adapt
     in
     let new_env = Environ.push_rel (name, None, t3) env in
     let sigma, p_rec = exact_modulo new_env sigma t2' t4' in
     sigma,
     mkLambda (Anonymous, thm,
	       mkLambda (name, t3,
			 mkApp ((adapt p_rec),
				[| mkApp (mkRel 2,
					  [| mkApp (unifproof,
						    [| mkRel 1 |])
					    |])
				  |])
			))
       
  | _ ->
     let sigma, return = Reductionops.infer_conv env sigma thm concl in
     if return then
       sigma, mkLambda (Anonymous, thm, mkRel 1)
     else
       Errors.error "Cannot unify."

let exact_modulo_tactic (_, proof) = (* Of what use is this evd _? *)
  Goal.nf_enter (* enter wouldn't work : Goal.concl goal wouldn't type check *)
    begin fun goal ->
	  let env = Goal.env goal in
	  let concl = Goal.concl goal in
	  Refine.refine (fun sigma ->
			 let thm = Retyping.get_type_of env sigma proof in
			 let sigma, imply = exact_modulo env sigma thm concl in
			 sigma, mkApp (imply, [| proof |])
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
