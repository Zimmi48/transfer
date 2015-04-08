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
                    
(* Do not forget to check type of proof *)
let add_surjection f g proof =
  let env = Global.env () in
  let sigma = Evd.empty in
  let proofterm = Constrintern.intern_reference proof in
  (* unsafe *)
  let thm, _ = Universes.type_of_global proofterm in
  let f_fun, _ = Constrintern.interp_constr env sigma (CRef (f,None)) in
  (* unsafe *)
  let f_typ = Retyping.get_type_of env sigma f_fun in
  let g_fun, _ = Constrintern.interp_constr env sigma (CRef (g,None)) in
  (* unsafe *)
  let g_typ = Retyping.get_type_of env sigma g_fun in
  let key =
    begin match kind_of_term f_typ, kind_of_term g_typ, kind_of_term thm with
	  | Prod (_, t1, t2), Prod(_, t3, t4), Prod(_, t5, t6) ->
	     begin try
		 Reduction.conv env t1 t4; (* modulo conversion *)
		 Reduction.conv env t2 t3;
		 Reduction.conv env t2 t5;
		 let eq_data = build_coq_eq_data () in
		 let t6 , args = decompose_app t6 in
		 if not (is_global eq_data.eq t6) then Errors.error "Bad proof";
		 begin match args with
		       | [ _ ; fgx ; x ] when isRelN 1 x ->
			  begin match kind_of_term fgx with
				| App (f , [| gx |]) ->
				   Reduction.conv env f f_fun;
				   begin match kind_of_term gx with
					 | App (g , [| x |]) when isRelN 1 x ->
					    Reduction.conv env g g_fun
					 | _ -> Errors.error "Bad proof."
				   end
				| _ -> Errors.error "Bad proof."
			  end
		       | _ -> Errors.error "Bad proof."
		 end;
	       with Reduction.NotConvertible -> Errors.error "Bad proof."
	     end;
	     t1 , t2
	  | _ -> Errors.error "Bad proof."
  end in
  surjections := PMap.add key
                          (f_fun, g_fun, Universes.constr_of_global proofterm)
                          !surjections
			  
let add_transfer f r r' proof =
  let env = Global.env () in
  let sigma = Evd.empty in
  let proofterm, _ = Constrintern.interp_constr env sigma proof in (* unsafe *)
  let thm = Retyping.get_type_of env sigma proofterm in
  let f_fun, _ = Constrintern.interp_constr env sigma f in (* unsafe *)
  let f_typ = Retyping.get_type_of env sigma f_fun in
  let r_rel, _ = Constrintern.interp_constr env sigma r in (* unsafe *)
  let r_typ = Retyping.get_type_of env sigma r_rel in
  let r'_rel, _ = Constrintern.interp_constr env sigma r' in (* unsafe *)
  let r'_typ = Retyping.get_type_of env sigma r'_rel in
  (* Do not forget to check type of proof *)
  let key = (r_rel, r'_rel) in
  transfers := PMap.add key (f_fun, proofterm) !transfers

exception UnifFailure
(* exact_modulo takes a theorem corresponding to a goal modulo isomorphism
   and construct a proof term for the goal *)
let rec exact_modulo env sigma thm concl : Evd.evar_map * Constr.t =
  match kind_of_term thm , kind_of_term concl with
  | App (f1 , l1) , App (f2 , l2) ->
     
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

  | Prod (name, t1, t2), Prod (_, t3, t4) ->
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
| [ "Declare" "Transfer" constr(f) constr(r) constr(r')
	      "by" constr(proof) ]
  -> [ add_transfer f r r' proof ]
END       

TACTIC EXTEND exact_modulo
| [ "exact" "modulo" open_constr(c) ]
  -> [ exact_modulo_tactic c ]
END
