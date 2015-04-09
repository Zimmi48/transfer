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
open Proofview
open Clenv
open Coqlib
open Constrexpr
open Globnames
       
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
(* Better error message would require knowing how to print a term. *)
let add_surjection f g proof =
  let env = Global.env () in
  let proofterm , thm = constr_and_type_of_ref proof in
  let f_fun , f_typ = constr_and_type_of_ref f in
  let g_fun , g_typ = constr_and_type_of_ref g in
  let key =
    match kind_of_term f_typ, kind_of_term g_typ, kind_of_term thm with
    | Prod (_, t1, t2), Prod(_, t3, t4), Prod(name, t5, t6) ->
       let name = string_of_name name in
       begin try
	   Reduction.conv env t1 t4; (* modulo conversion *)
	   Reduction.conv env t2 t3;
	   Reduction.conv env t2 t5;
	   let eq_data = build_coq_eq_data () in
	   let t6 , args = decompose_app t6 in
	   if not (is_global eq_data.eq t6) then
	     Errors.error "Theorem is not an equality.";
	   begin match args with
		 | [ _ ; fgx ; x ] when isRelN 1 x ->
		    begin match kind_of_term fgx with
			  | App (f , [| gx |]) ->
			     Reduction.conv env f f_fun;
			     begin match kind_of_term gx with
				   | App (g , [| x |]) when isRelN 1 x ->
				      Reduction.conv env g g_fun
				   | _ -> Errors.error ("In theorem, the term under f should be (g " ^ name ^ ").")
			     end
			  | _ -> Errors.error ("In theorem, the left-hand side of the equality should be f (g " ^ name ^ ").")
		    end
		 | _ -> Errors.error ("In theorem, the right-hand side of the equality should be " ^ name ^ ".")
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
			   with Reduction.NotConvertible -> Errors.error ("In conclusion, argument " ^ string_of_int (i + 1) ^ " should be (f " ^ (List.nth args (n - i - 1)) ^ ").")
			 done			 
		       with Reduction.NotConvertible -> Errors.error "The hypothesis and conclusion should be formed of the appropriate relation applied to arguments."
		     end
		  | _ -> Errors.error "The theorem has a wrong form."
	    end
	 | _ -> Errors.error "Some arguments have a wrong type."
       in
       check r_typ r'_typ thm []
  in
  let key = (r_rel, r'_rel) in
  transfers := PMap.add key (f_fun, proofterm) !transfers

exception UnifFailure
(* exact_modulo takes a theorem corresponding to a goal modulo isomorphism
   and construct a proof term for the goal *)
let rec exact_modulo env sigma thm concl : Evd.evar_map * Constr.t =
  match kind_of_term thm , kind_of_term concl with
  | App (f1 , l1) , App (f2 , l2) -> failwith "app";
     
     (* OLD CODE BEGINS
         let sigma , e = exact_modulo env sigma holes f1 f2 in
         let sigma , el = List.fold_left2 (fun (sigma, acc) t1 t2 ->
                          let sigma , e =
                            exact_modulo env sigma holes t1 t2 in
                          sigma , e :: acc
                         ) (sigma, []) (Array.to_list l1) (Array.to_list l2)
         in
         (* coq_eq_rect has not the right type *)
         sigma , mkApp (mkConst (coq_eq_rect ()), [|failwith "TODO"|])
         OLD CODE ENDS *)
     
     (* try exact match first *)
     if Constr.equal f1 f2 then
       (* the relation f1 f2 must correspond : exactly or modulo conversion? *)
       failwith "TODO: check unification -> proof term reflexivity"
     else (* there may be a transfer required *)
       begin try
	   let (surj, proof) = PMap.find (f1, f2) !transfers in
	   failwith "TODO: construct proof term"
	 with Not_found -> raise UnifFailure
       end

  | Prod (name, t1, t2), Prod (_, t3, t4) -> failwith "prod";
     let sigma, return = Reductionops.infer_conv env sigma t1 t3 in
     if return then (* if t1 = t3 *)
       let new_env = Environ.push_rel (name, None, t1) env in
       let sigma, p_rec = exact_modulo new_env sigma t2 t4 in
       failwith "TODO: construct proof term"
     else (* there may be a transfer required *)
       begin try
	   let (surj, inv, proof) = PMap.find (t1, t3) !surjections in
	   failwith "TODO: recursive call"
	 with Not_found -> raise UnifFailure
       end
  | _ ->
     let sigma, return = Reductionops.infer_conv env sigma thm concl in
     if return then
       sigma, Universes.constr_of_global (build_coq_eq_data ()).refl
     else
       Errors.error "Cannot unify."

let exact_modulo_tactic (_, thm) = (* Of what use is this evd _? *)
  Goal.nf_enter (* enter wouldn't work : Goal.concl goal wouldn't type check *)
    begin fun goal ->
	  let env = Goal.env goal in
	  let concl = Goal.concl goal in
	  Refine.refine (fun sigma -> exact_modulo env sigma thm concl)
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
