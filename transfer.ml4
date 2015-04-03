(* Apply a theorem modulo isomorphism *)
(* Copyright Théo Zimmermann 2015     *)
(* How to use (with Coq8.5beta1):
 * $ coq_makefile transfer.ml4 -o Makefile
 * $ make
 * $ coqtop -load-ml-object transfer.cmxs
 * Coq < Declare ML Module "transfer_plugin".
 *)

(*i camlp4use: "pa_extend.cmo" i*)
(*i camlp4deps: "grammar/grammar.cma" i*)

DECLARE PLUGIN "transfer_plugin"

open Names
open Term
       
(* Why should we have to redifine module Constr?
 * There is probably a better way *)
module Constr =
  struct
    type t = constr
    let compare x y = compare (hash_constr x) (hash_constr y)
  end
    
module ConstrMap = Map.Make(Constr)
(* This extra step is needed so that empty has not a polymorphic type
 * and can be used inside a Map *)		   
let empty : (constr * identifier * constr) ConstrMap.t = ConstrMap.empty
			   
let surjections = ref empty
let transfers = ref empty

(* Do not forget to check type of proof *)
let add_surjection f proof = ()

(* Do not forget to check type of proof *)
let add_transfer f r r' proof = ()

let apply_modulo thm =
  Proofview.Goal.nf_enter (* or enter ? *)
    begin fun goal ->
	  Proofview.Refine.refine
	    begin fun sigma ->
		  sigma , mkApp (snd thm, [||])
	    end
    end
				  
VERNAC COMMAND EXTEND DeclareSurjection
| [ "Declare" "Surjection" ident(f) "by" constr(proof) ]
  -> [ add_surjection f proof ]
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
