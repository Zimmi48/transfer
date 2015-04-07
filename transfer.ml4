(* Apply a theorem modulo isomorphism *)
(*   Copyright Théo Zimmermann 2015   *)

(* How to use (with Coq 8.5 trunk):
 * $ coq_makefile transfer.ml4 -o Makefile
 * $ make
 * $ coqtop -load-ml-object transfer.cmxs
 * Coq < Declare ML Module "t".
 *)

(*i camlp4use: "pa_extend.cmo" i*)
(*i camlp4deps: "grammar/grammar.cma" i*)

DECLARE PLUGIN "t"

open Names
open Term
open Proofview
open Clenv
       
module PairConstr =
  struct
    type t = constr * constr
    let compare (x1, x2) (y1, y2) =
      match Constr.compare x1 y1 with (* compare is defined on constr *)
      | 0 -> compare x2 y2
      | x -> x
    (* or should we rather test for conversion?*)
  end
    
module PairConstrMap = Map.Make(PairConstr)
(* This extra step is needed so that empty has not a polymorphic type
 * and can be used inside a Map *)
let empty_surj : (constr * constr * constr) PairConstrMap.t =
  PairConstrMap.empty
let empty_transf :
      (identifier * identifier * identifier * constr) PairConstrMap.t =
  PairConstrMap.empty

let surjections = ref empty_surj
let transfers = ref empty_transf
		    
(* Do not forget to check type of proof *)
let add_surjection f g proof =
  let env = Global.env () in
  let sigma = Evd.empty in
  let proofterm, _ = Constrintern.interp_constr env sigma proof in (* unsafe *)
  let thm = Retyping.get_type_of env sigma proofterm in
  (*let f_fun = mkVar f in*)
  let f_fun, _ = Constrintern.interp_constr env sigma f in (* unsafe *)
  let f_typ = Retyping.get_type_of env sigma f_fun in
  (* Anomaly : variable f unbound. *)
  (*let g_fun = mkVar g in*)
  let g_fun, _ = Constrintern.interp_constr env sigma g in (* unsafe *)
  let g_typ = Retyping.get_type_of env sigma g_fun in
  match kind_of_term f_typ, kind_of_term g_typ, kind_of_term thm with
  | Prod (_, t1, t2), Prod(_, t3, t4), Prod(_, t5, t6) when
	 Constr.equal t1 t4 &&		      
	   Constr.equal t2 t3 &&
	     Constr.equal t2 t5 ->
     (* or should we rather test for conversion? *)
     (*let eq = mkApp (
		  failwith "TODO" (* mkConst (Name (Id.of_string "eq")) *),
		  [| t2 ;
		     mkApp (f_fun ,  [| mkApp (g_fun , [| mkRel 1 |]) |] );
		     mkRel 1 |] ) in*)
     if true (*Constr.equal t6 eq*) then
       let key = (t1, t2) in
       surjections := PairConstrMap.add key
					(f_fun, g_fun, proofterm)
					!surjections
     else failwith "Bad proof"
  | _ -> failwith "Bad proof"
         (* Exceptions are not the right way to report that *)
  
(* Do not forget to check type of proof *)
let add_transfer f r r' proof =
  let env = Global.env () in
  let sigma = Evd.empty in
  let proofterm, _ = Constrintern.interp_constr env sigma proof in (* unsafe *)
  let key = failwith "TODO" in
  transfers := PairConstrMap.add key (f, r, r', proofterm) !transfers

let unify_modulo env sigma hole_types cl_concl concl = failwith "TODO"

let apply_modulo thm =
  Goal.nf_enter (* or enter ? *)
    (fun goal ->
     let env = Goal.env goal in
     let concl = Goal.concl goal in
     Refine.refine
       (fun sigma ->
	let t = Retyping.get_type_of env sigma concl in
	let sigma', cl = Clenv.make_evar_clause env sigma t in
	let sigma'', e, el =
	  unify_modulo env sigma
		       (List.map (fun h -> h.hole_type) cl.cl_holes)
		       cl.cl_concl concl in
	sigma'' , mkApp (snd thm, [||])
       )
    )
				  
VERNAC COMMAND EXTEND DeclareSurjection
| [ "Declare" "Surjection" constr(f) "by" "(" constr(g) "," constr(proof) ")" ]
  -> [ add_surjection f g proof ]
END

VERNAC COMMAND EXTEND DeclareTransfer
| [ "Declare" "Transfer" ident(f) ident(r) ident(r')
	      "by" constr(proof) ]
  -> [ add_transfer f r r' proof ]
END       

TACTIC EXTEND apply_modulo
| [ "apply" "modulo" open_constr(c) ]
  -> [ apply_modulo c ]
END
