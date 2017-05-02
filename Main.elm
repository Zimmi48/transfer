module Main exposing (..)

import Css exposing (..)
import Css.Elements exposing (..)
import Html exposing (Html)
import Html.Attributes
import Markdown
import Slides exposing (slidesDefaultOptions)


title : List (Html msg)
title =
    [ md """

# Automatic and Transparent Transfer of Theorems along (Iso)morphisms in the Coq Proof Assistant

Théo Zimmermann

Deducteam Seminar
April 27, 2017

""" ]


introduction : List (Html msg)
introduction =
    [ md """

  ## Who am I?

  * First year PhD student at IRIF / πr²,
  * Supervised by Hugo Herbelin,
  * Participating in the development of Coq.

  """
    , md """

  ### My research objectives

  Making Coq easier to do math with
  (without a complicated training).

  """
    ]


transferIntro : List (Html msg)
transferIntro =
    [ md """

  ## This talk

  ### Transfer of theorems

  * Work started as an intern in 2015.
  * Library available at:
    https://github.com/Zimmi48/transfer
  * Still experimental: *please send me your questions / remarks*.

  """ ]


outline : List (Html msg)
outline =
    [ md """

  ## Outline of this talk

  * What **issue** is the transfer library solving?
  * **User perspective** on the transfer library.
  * **Logic behind** the transfer library.
  * **Applications** of the transfer library.
  * How to **program** such tactics?

  """ ]


representationIssue : List (Html msg)
representationIssue =
    [ md """

  ## The representation issue

  * When formalizing math on computer, *choices of representation are necessary*.
    E.g. in Coq unary `nat` vs binary `BinNums.N`, unary `ssrint.int` vs binary `BinNums.Z`.

  """, md """

  * Also when constructing mathematical structures (on paper).
  E.g. Cauchy sequences vs Dedekind cuts.

  """ ]


axiomatization : List (Html msg)
axiomatization =
    [ md """

  ## The axiomatization approach

  Abstracting away from the representation.

  * Preferred solution in math.
  * Doable in Coq with modules or typeclasses.
  * Equations instead of function definitions.

  """
    , Html.div []
        [ Html.p
            [ [ textAlign left ] |> asPairs |> Html.Attributes.style ]
            [ Html.span
                [ [ rgb 0 255 0 |> color
                  , position relative
                  , px 15 |> right
                  ]
                    |> asPairs
                    |> Html.Attributes.style
                ]
                [ Html.text "➕" ]
            , Html.span [] [ Html.text "Some behaviors can be left unspecified." ]
            ]
        , Html.p
            [ [ textAlign left ] |> asPairs |> Html.Attributes.style ]
            [ Html.span
                [ [ rgb 255 0 0 |> color
                  , position relative
                  , px 15 |> right
                  ]
                    |> asPairs
                    |> Html.Attributes.style
                ]
                [ Html.text "➖" ]
            , Html.span [] [ Html.text "No proof by computation is possible." ]
            ]
        , Html.p
            [ [ textAlign left ] |> asPairs |> Html.Attributes.style ]
            [ Html.span
                [ [ rgb 255 0 0 |> color
                  , position relative
                  , px 15 |> right
                  ]
                    |> asPairs
                    |> Html.Attributes.style
                ]
                [ Html.text "➖" ]
            , Html.span [] [ Html.text "Rewriting with an equivalence (vs equality)." ]
            ]
        ]
    ]


transferApproach : List (Html msg)
transferApproach =
    [ md """

  ## The transfer approach

  * Work on a specific representation.
  * **Transfer results automatically**, using knowledge on the relation between the representations.

  """
    , Html.div []
        [ Html.p
            [ [ textAlign left ] |> asPairs |> Html.Attributes.style ]
            [ Html.span
                [ [ rgb 0 255 0 |> color
                  , position relative
                  , px 15 |> right
                  ]
                    |> asPairs
                    |> Html.Attributes.style
                ]
                [ Html.text "➕" ]
            , Html.span []
                [ Html.text "Allow to merge independent developments " ]
            , Html.span
                [ [ fontStyle italic ] |> asPairs |> Html.Attributes.style ]
                [ Html.text "(see applications later)" ]
            , Html.span [] [ Html.text "." ]
            ]
        , Html.p
            [ [ textAlign left ] |> asPairs |> Html.Attributes.style ]
            [ Html.span
                [ [ rgb 0 255 0 |> color
                  , position relative
                  , px 15 |> right
                  ]
                    |> asPairs
                    |> Html.Attributes.style
                ]
                [ Html.text "➕" ]
            , Html.span []
                [ Html.text "Explicit transfer sometimes useful in math " ]
            , Html.span
                [ [ fontStyle italic ] |> asPairs |> Html.Attributes.style ]
                [ Html.text "(see applications later)" ]
            , Html.span [] [ Html.text "." ]
            ]
        ]
    ]


definitions : List (Html msg)
definitions =
    [ md """

  ## Preliminary definitions

  `Related` is boilerplate:

    Related R x y := R x y

  It is a generalization of `Proper`:

    Proper R x := R x x

  `##>` is a generalization of `==>`:

    (R ##> S) f g := ∀ x y, R x y → S (f x) (g y)

  """ ]


transferUser : List (Html msg)
transferUser =
    [ md """

  ## Transfer library

  ### User perspective

  Declaring an isomorphism between A and B.

  Given a function `f : B → A`,

    Definition R x y := x = f y.
    Instance biunique : Related (R ##> R ##> iff) eq eq.
    Instance bitotal : Related ((R ##> iff) ##> iff) all all.
    Instance constants : ∀ y : B, Related R (f y) y.

  """ ]


transferUserWeak : List (Html msg)
transferUserWeak =
    [ md """

  ## Transfer library

  ### User perspective

  Or some weaker relation:

    Instance rightunique :
      Related (R ##> R ##> impl) eq my_eq.
    Instance righttotal :
      Related ((R ##> impl) ##> impl) all ball.

  """ ]


respectfulFunctional : List (Html msg)
respectfulFunctional =
    [ md """

  ## Unfolding respectful

  Right-uniqueness = functionality:

    Related (R ##> R ##> impl) eq my_eq
      = ∀ (x1 : A) (y1 : B), R x1 y1 →
        ∀ (x2 : A) (y2 : B), R x2 y2 →
        x1 = x2 → my_eq y1 y2

  Left-uniqueness = injectivity.
  Bi-uniqueness = both.

  """ ]


respectfulTotal : List (Html msg)
respectfulTotal =
    [ md """

  ## Unfolding respectful

  Right-totality = surjectivity.

  The following is always true:

    Related ((R ##> impl) ##> impl) all ball
      = ∀ (P : A → Prop) (Q : B → Prop),
          (∀ (x : A) (y : B), R x y → P x → Q y) →
          (∀ x : A, P x) → ball Q

    ball P := ∀ y : B, (∃ x : A, R x y) → P y

  """ ]


transferMorphism : List (Html msg)
transferMorphism =
    [ md """

  ## Transfer library

  ### User perspective

  For which functions / relations is `R` a morphism?

    Instance suc_morphism : Related (R ##> R) A.suc B.suc.
    Instance add_morphism : Related (R ##> R ##> R) A.add B.add.
    Instance leq_morphism : Related (R ##> R ##> iff) A.leq B.leq.

  """ ]


transferTactic : List (Html msg)
transferTactic =
    [ md """

  ## The `transfer` tactic

    1 subgoal
      ============================
      ∀ (x y z : B), B.leq x y → B.leq y z → B.leq x z
    Coq < transfer.
    1 subgoal
      ============================
      ∀ (x y z : A), A.leq x y → A.leq y z → A.leq x z

  """ ]


transferTactic2 : List (Html msg)
transferTactic2 =
    [ md """

  ## The `transfer` tactic

    1 subgoal
      x y : B
      ============================
      B.add (B.suc x) y = B.suc (B.add x y)
    Coq < transfer.
    1 subgoal
      x y : B
      ============================
      A.add (A.suc (f x)) (f y) = A.suc (A.add (f x) (f y))

  """ ]


exactTactic : List (Html msg)
exactTactic =
    [ md """

  ## The `exactm` tactic

    1 subgoal
      ============================
      ∀ P : N → Prop, P 0%N → (∀ n : N, P n → P (N.succ n)) →
      ∀ n : N, P n.
    Coq < exactm nat_ind.
    No more subgoals.

  """ ]


implementationLogic : List (Html msg)
implementationLogic =
    [ md """

  ## Implementation logic

  * Strongly inspired by Sozeau's generalized rewriting.
  * Generalization to the heterogeneous case inspired by Cohen, Dénès and Mörtberg's *"Refinements for free!".*
  * Same ideas also found in Isabelle's transfer package (by Huffman and Kunčar).

  """ ]


introElimRules : List (Html msg)
introElimRules =
    [ md """

  ## Inference rules

  (from Huffman and Kunčar, 2013)

  ![Respectful arrow introduction rule](respectful_intro.png)
  ![Respectful arrow elimination rule](respectful_elim.png)

  Plus transfer rules for constants:

    Instance impl_transfer : (iff ##> iff ##> iff) impl impl.

  """ ]


structuralRules : List (Html msg)
structuralRules =
    [ md """

  ## Inference rules

  In the form of structural typing rules
  (from Huffman and Kunčar, 2013)

  ![Application rule](app_rule.png)
  ![Abstraction rule](lam_rule.png) ![Variable rule](var_rule.png)

  """ ]


myRules : List (Html msg)
myRules =
    [ md """

  ## Inference rules

  With the proofs
  (from Zimmermann and Herbelin, 2015)

  ![Rules with proofs](my_rules.png)

  """ ]


rewritingRules : List (Html msg)
rewritingRules =
    [ md """

  ## Inference rules

  Of generalized rewriting (from Sozeau, 2010)

  ![Rewriting rules](sozeau_rules.png)

  """ ]


example : List (Html msg)
example =
    [ md """

  ## Rules applied to an example

    Related iff ? (∀ x : B, B.leq x B.0 → x = B.0)

  """
    , md """

  transformed into (Forall, App and Lambda):

    x0 : A, x : B, Hx : Related R x0 x
    ============================
    Related iff ? (B.leq x B.0 → x = B.0)

    ============================
    Related ((R ##> iff) ##> iff) all all

  """
    ]


example2 : List (Html msg)
example2 =
    [ md """

  ## Rules applied to an example

    Related iff ? (B.leq x B.0 → x = B.0)

  """
    , md """

  transformed into (App):

    Related iff ? (B.leq x B.0)
    Related iff ? (x = B.0)
    Related (iff ##> iff ##> iff) impl impl

  """
    ]


example3 : List (Html msg)
example3 =
    [ md """

  ## Rules applied to an example

    Related iff ? (B.leq x B.0)
    Related iff ? (x = B.0)

  """
    , md """

  transformed into (App):

    Related R x0 x
    Related R (f B.0) B.0
    Related (R ##> R ##> iff) A.leq B.leq
    Related (R ##> R ##> iff) eq eq

  """
    ]


implementation : List (Html msg)
implementation =
    [ md """

  ## Implementation

  * Structural recursion
    (following the inference rules).
  * Existential variables
    (solved by unification).
  * Proof-search with backtracking.

  """ ]


applicationMagaud : List (Html msg)
applicationMagaud =
    [ md """

  ## Application: new domains for existing decision procedures

  (by Magaud, presented at CoqPL 2017)

  * Transfer rules between `Z` and `ssrint`.
  * Allow to use `omega`, `lia`, `psatz`... on `ssrint`.
  * Much easier than e.g. changing `omega`'s implementation to make it polymorphic.

  """ ]


difficultyMagaud : List (Html msg)
difficultyMagaud =
    [ md """

  ## Application: new domains for existing decision procedures

  How to relate propositional relation `Z.lt` and boolean relation `Num.lt`?

    Instance prop_bool : Related (reflect ##> iff) id is_true.
    Instance lt_transfer_rule :
      Related (R ##> R ##> reflect) Z.lt Num.lt.

  * Limited to one direction of transfer.
  * Some post-transfer reduction is required.

  """ ]


applicationRaggi : List (Html msg)
applicationRaggi =
    [ md """

  ## Application: mechanizing proofs with inherent transfer

  *"Automating change of representation for proofs in discrete mathematics."*
  (by Raggi, Bundy, Grov and Pease)

  * **Numbers as bags of primes.**
    To prove properties related to divisors.
  * **Numbers as sets.**
    To translate combinatorial proofs of equalities between numbers.

  """ ]


difficultyRaggi : List (Html msg)
difficultyRaggi =
    [ md """

  ## Application: mechanizing proofs with inherent transfer

  How to relate addition on numbers
  and *disjoint* union on sets?

  Incorrect:

    Related (R ##> R ##> R) add union

  Raggi's approach (with pre / post-processing):

    Related (R ##> R ##> R ##> iff) is_sum is_disj_union

  """ ]


typeclasses : List (Html msg)
typeclasses =
    [ md """

  ## Programming tactics with `typeclasses eauto`

  * Proof-search behind Coq's typeclasses.
  * Can be seen as a sort of Coq's Prolog.
  * Can be used as a tactic language
    (see my presentation at TTT 2017).

  """
    , Html.div []
        [ Html.p
            [ [ textAlign left ] |> asPairs |> Html.Attributes.style ]
            [ Html.span
                [ [ rgb 0 255 0 |> color
                  , position relative
                  , px 15 |> right
                  ]
                    |> asPairs
                    |> Html.Attributes.style
                ]
                [ Html.text "➕" ]
            , Html.span [] [ Html.text "Very concise programming, very readable." ]
            ]
        , Html.p
            [ [ textAlign left ] |> asPairs |> Html.Attributes.style ]
            [ Html.span
                [ [ rgb 255 0 0 |> color
                  , position relative
                  , px 15 |> right
                  ]
                    |> asPairs
                    |> Html.Attributes.style
                ]
                [ Html.text "➖" ]
            , Html.span [] [ Html.text "Hard to debug puzzling behaviors." ]
            ]
        , Html.p
            [ [ textAlign left ] |> asPairs |> Html.Attributes.style ]
            [ Html.span
                [ [ rgb 255 0 0 |> color
                  , position relative
                  , px 15 |> right
                  ]
                    |> asPairs
                    |> Html.Attributes.style
                ]
                [ Html.text "➖" ]
            , Html.span [] [ Html.text "Critical reliance on Coq's unification." ]
            ]
        ]
    ]


subrel : List (Html msg)
subrel =
    [ md """

  ## Sub-relations

  `iff` is a sub-relation of `impl`. Why not add:

     Related R x y → Subrel R S → Related S x y

  Explosion of the proof-search space!
  (= slow failure)

  * Solved by limiting where this rule is applied.
  * Or having `iff` mode / `impl` mode.

  """ ]


flip : List (Html msg)
flip =
    [ md """

  ## Flip in `impl` mode

    Related impl ? (B.leq x B.0 → x = B.0)

  """
    , md """

  transformed into:

    Related (flip impl) ? (B.leq x B.0)
    Related impl ? (x = B.0)
    Related (flip impl ##> impl ##> impl) impl impl

  """
    ]


flip2 : List (Html msg)
flip2 =
    [ md """

  ## Flip in `impl` mode

    Related (flip impl) ? (B.leq x B.0)

  """
    , md """

  transformed into:

    Related impl (B.leq x B.0) ?

  thanks to:

    flip_rule : Related R x y → Related (flip R) y x

  """
    ]


flip3 : List (Html msg)
flip3 =
    [ md """

  ## Flip in `impl` mode

    Related impl (B.leq x B.0) ?

  transformed into:

    Related (flip R) x ?
    Related (flip R) B.0 ?
    Related (flip R ##> flip R ##> impl) B.leq A.leq

  """ ]


perspectives : List (Html msg)
perspectives =
    [ md """

  ## On-going and future work

  * More on performance and usability.
  * More transfer rules.
  * Separating rules into distinct hint databases to give more control to the user.
  * Generalizing `apply` to work transparently modulo (iso)morphism.

  """ ]


references : List (Html msg)
references =
    [ Html.small
        [ [ lineHeight (pct 120) ] |> asPairs |> Html.Attributes.style ]
        [ md """

  ## References

  * Sozeau, M. (2010). **A new look at generalized rewriting in type theory.** J of Formalized Reasoning, 2(1), 41–62.
  * Cohen, C., Dénes, M., & Mörtberg, A. (2013). **Refinements for free!** CPP (pp. 147-162).
  * Huffman, B., & Kunčar, O. (2013). **Lifting and Transfer: A modular design for quotients in Isabelle/HOL.** CPP (pp. 131-146).
  * Raggi, D., Bundy, A., Grov, G., & Pease, A. (2015). **Automating change of representation for proofs in discrete mathematics.** CICM (pp. 227-242).
  * Zimmermann, T., & Herbelin, H. (2015). **Automatic and Transparent Transfer of Theorems along Isomorphisms in the Coq Proof Assistant.** CICM (work-in-progress track).
  * Magaud, N. (2017). **Transferring Arithmetic Decision Procedures (on Z) to Alternative Representations.** POPL (CoqPL workshop).
  * Zimmermann, T., & Herbelin, H. (2017). **Coq's Prolog and application to defining semi-automatic tactics.** POPL (TTT workshop).

  """ ]
    ]


main : Program Never Slides.Model Slides.Msg
main =
    [ title
    , introduction
    , transferIntro
    , outline
    , representationIssue
    , axiomatization
    , transferApproach
    , definitions
    , transferUser
    , transferUserWeak
    , respectfulFunctional
    , respectfulTotal
    , transferMorphism
    , transferTactic
    , transferTactic2
    , exactTactic
    , implementationLogic
    , introElimRules
    , structuralRules
    , myRules
    , rewritingRules
    , example
    , example2
    , example3
    , implementation
    , applicationMagaud
    , difficultyMagaud
    , applicationRaggi
    , difficultyRaggi
    , typeclasses
    , subrel
    , flip
    , flip2
    , flip3
    , perspectives
    , references
    ]
        |> List.map Slides.htmlFragments
        |> Slides.app { slidesDefaultOptions | style = myStyle }


md : String -> Html msg
md =
    Markdown.toHtmlWith
        { githubFlavored = Just { tables = True, breaks = True }
        , defaultHighlighting = Nothing
        , sanitize = False
        , smartypants = True
        }
        []


myStyle : List Css.Snippet
myStyle =
    [ body
        [ padding zero
        , margin zero
        , height (pct 100)
        , backgroundColor (hex "effafa")
        , color (rgb 0 0 0)
        , fontFamilies [ qt "Open Sans", sansSerif.value ]
        , fontSize (px 36)
        , fontWeight (int 400)
        , textAlign center
        , lineHeight (pct 150)
        ]
    , h1
        [ fontWeight (int 600)
        , marginTop (px 150)
        ]
    , h2
        [ fontWeight (int 600)
        ]
    , h4
        [ marginBottom (px -30)
        ]
    , section
        [ height (px 700)
        , width (px 960)
        , property "background-position" "center"
        , property "background-size" "cover"
        , displayFlex
        , property "justify-content" "center"
        , alignItems left
        ]
    , footer
        [ fontSize (px 22)
        , lineHeight (pct 130)
        ]
    , p
        [ margin (px 15)
        ]
    , li
        [ textAlign left
        ]
    , (.) "slide-content"
        [ margin2 zero (px 90)
        ]
    , code
        [ fontFamilies [ qt "Nova Mono", monospace.value ]
        , color (rgb 0 100 255)
        ]
    , pre
        [ textAlign left
        , padding (px 12)
        , fontSize (px 26)
        ]
    , a
        [ color (rgb 0 0 0)
        ]
    , table
        [ margin2 zero auto
        ]
    , th
        [ padding2 zero (px 25)
        , fontWeight (int 400)
          -- no bold by default in table header
        ]
    ]
