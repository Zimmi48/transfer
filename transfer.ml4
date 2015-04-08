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
open Program
       
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
let empty : (constr * constr * constr) PairConstrMap.t = PairConstrMap.empty

let surjections = ref empty
let transfers = ref empty
                    
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

exception Unif_failure
(* exact_modulo takes a theorem corresponding to a goal modulo isomorphism
   and construct a proof term for the goal *)
let rec exact_modulo env sigma thm cl concl =
  match kind_of_term thm , kind_of_term concl with
  | Lambda (_, t1, c1) , Lambda (_, t2, c2) ->
     (* exact match *)
     (* extend environment before recursive call *)
     failwith "TODO"
  | App (f1 , l1) , App (f2 , l2) ->
     (* try exact match first *)
     (* the relation f1 f2 must correspond : exactly or modulo conversion? *)
     begin try
	 (*
         let sigma , e = exact_modulo env sigma holes f1 f2 in
         let sigma , el = List.fold_left2 (fun (sigma, acc) t1 t2 ->
                          let sigma , e =
                            exact_modulo env sigma holes t1 t2 in
                          sigma , e :: acc
                         ) (sigma, []) (Array.to_list l1) (Array.to_list l2)
         in
         (* coq_eq_rect has not the right type *)
         sigma , mkApp (mkConst (coq_eq_rect ()), [|failwith "TODO"|])
          *)
	 failwith "TODO"
       with Unif_failure ->
	 (* there may be a transfer required *)
	 failwith "TODO"
     end
  | Prod (_, t1, t2), Prod (_, t3, t4) ->
     (* try exact match first *)
     (* t1 and t3 must correspond: exactly or modulo conversion? *)
     begin try
	 failwith "TODO"
       with Unif_failure ->
	    (* there may be a transfer required *)
	    failwith "TODO"
     end
  | _ -> failwith "TODO"

let exact_modulo_tactic (sigma, thm) = (* Of what use is this sigma? *)
  Goal.nf_enter (* or enter ? *)
    (fun goal ->
     let env = Goal.env goal in
     let concl = Goal.concl goal in (* what is concl exactly? *)
     Refine.refine
       (fun sigma -> (* sigma has been masked *)
        let t = Retyping.get_type_of env sigma concl in
        let sigma, cl = Clenv.make_evar_clause env sigma t in
        exact_modulo env sigma thm cl concl
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

TACTIC EXTEND exact_modulo
| [ "exact" "modulo" open_constr(c) ]
  -> [ exact_modulo_tactic c ]
END
