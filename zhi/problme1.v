Require Export ZArith.
Require Export Coq.Arith.Compare_dec.
Require Export Coq.Lists.List.
Require Export X_SparkTactics.
(* Require Export Coq.Bool.Bool. *)

(**********************************

   Problem 1: Patience Solitaire
   
   Proof by Zhi Zhang

 **********************************)

Print nat_compare.
Print leb.


Definition Index := nat.
(* for each element, we also record its original index, which is used to track
   whether one elemnt is preceding another;
*)
Definition Stack := list (Index * nat).
Definition Stacks := list Stack.
Definition EmptyStacks: Stacks := nil.


(**********************************

       Relational Version

 **********************************)

Inductive Insert_Rule: (Index * nat) -> Stacks -> Stacks -> Prop := 
  | Inert_to_Head: forall stack i' n' ns n i stacks,
      stack = ((i', n') :: ns) ->
      leb n n' = true -> 
      Insert_Rule (i, n) (stack :: stacks) (((i, n) :: stack) :: stacks)
  | Inert_to_Tail: forall stack i' n' ns n i stacks stacks',
      stack = ((i', n') :: ns) ->
      leb n n' = false -> 
      Insert_Rule (i, n) stacks stacks' ->
      Insert_Rule (i, n) (stack :: stacks) (stack :: stacks')
  | Insert_to_Empty: forall i n,
      Insert_Rule (i, n) nil (((i, n) :: nil) :: nil).

Inductive PatienceSolitaire_Rule: list (Index * nat) -> Stacks -> Stacks -> Prop := 
  | Cards_NonEmpty: forall card stacks stacks' cards stacks'',
      Insert_Rule card stacks stacks' ->
      PatienceSolitaire_Rule cards stacks' stacks'' -> 
      PatienceSolitaire_Rule (card :: cards) stacks stacks''
  | Cards_Empty: forall stacks,
      PatienceSolitaire_Rule nil stacks stacks.



(********************************************************************************
   < Lemma 1 >
   
   To each element in stack i+ 1, there is an element in stack i that precedes it, 
   so that by chaining these elements, we can construct an increasing subsequence 
   of length n;
 ********************************************************************************)

Require Import Coq.Init.Datatypes.

Definition default: Stack := nil.

Section Auxiliary.

  (* Precede stack stack': for each element in stack', there is an element
     in stack that precedes it; 
   *)
  Inductive Precede: Stack -> Stack -> Prop :=
    | Precede_NonEmpty: forall stack i' n' stack',
        (exists i n, In (i, n) stack -> i <= i' /\ n <= n') ->
        Precede stack stack' ->
        Precede stack ((i', n') :: stack')
    | Precede_Empty: forall stack,
        Precede stack nil.

  
  Lemma Add_Reserved: forall stack stack' a,
    Precede stack stack' ->
      Precede (a :: stack) stack'.
  Proof.    
    (* ########### To Be Proved, which looks obvious *)
    admit. 
  Qed.


  Function Append (stacks: Stacks) (a: (Index * nat)): Stacks :=
    match stacks with
    | (stack :: stacks') =>
        stack :: (Append stacks' a)
    | nil => (a :: nil) :: nil
    end.
  
  Lemma Insert_Rule_Property: forall a stacks stacks',
    Insert_Rule a stacks stacks' ->
      length stacks' = length stacks \/ (stacks' = Append stacks a).
  Proof.
    intros.
    induction H; smack.
  Qed.


  (* if the stacks has "Precede" property, then after inserting an element
     a into the stack according to Patience Solitaire rules, then the result
     stack' should also reserve the "Precede" property.
  *)
  Lemma Precede_Reserved: forall a stacks stacks' i,
    Insert_Rule a stacks stacks' ->
    (forall j, j >= 1 -> j <= ((length stacks) - 1) -> 
               Precede (nth (j-1) stacks default) (nth j stacks default)) ->  
    i >= 1 ->
    i <= ((length stacks') - 1) ->
    Precede (nth (i - 1) stacks' default) (nth i stacks' default).
  Proof.
(*
    intros. 
    destruct H; smack.
    specialize (H0 i H1 H2).
    destruct i; smack.
    destruct i; smack.
    apply Add_Reserved; auto.
    specialize (Insert_Rule_Property (i0, n) stacks stacks' H4).
    smack.
    rewrite H5 in *.
    specialize (H0 i H1 H2).
    destruct i; smack.
    destruct i; smack.
*)
    intros a stacks stacks' i H. revert i.
    induction H; smack.
  - specialize (H1 i0 H2 H3).
    destruct i0; smack.
    destruct i0; smack.
    apply Add_Reserved; auto.
  - specialize (Insert_Rule_Property (i, n) stacks stacks' H1).
    smack.
    rewrite H5 in *.
    specialize (H2 i0 H3 H4).
    destruct i0; smack.
    destruct i0; smack.    
    
    
    
  Qed.

 
End Auxiliary.



Lemma lemma1: forall cards InitialStacks ResultStacks i,
  PatienceSolitaire_Rule cards InitialStacks ResultStacks ->
  (* requirement for the initial stack *)
  (forall j, j >= 2 -> j <= length InitialStacks -> 
             Precede (nth (j-1) InitialStacks default) (nth j InitialStacks default)) ->
  i >= 2 -> 
  i <= length ResultStacks ->
  Precede (nth (i-1) ResultStacks default) (nth i ResultStacks default).
Proof.
  induction cards.
- intros.
  inversion H; subst.
  specialize (H0 i H1 H2).
  smack.
- intros.
  inversion H; subst.
  specialize (IHcards stacks' ResultStacks i H8).
  apply IHcards; clear IHcards; smack.
  admit.


  .
  
Qed.

(*
Lemma lemma1: forall cards InitialStacks ResultStacks i stack_i stack_i_minus_1,
  PatienceSolitaire_Rule cards InitialStacks ResultStacks ->
  (* requirement for the initial stack *)
  (forall j, j >= 2 -> j <= length InitialStacks -> 
             Precede (nth j ResultStacks default) (nth (j - 1) ResultStacks default)) ->
  i >= 2 -> 
  i <= length ResultStacks ->
  nth i ResultStacks default = stack_i ->
  nth (i-1) ResultStacks default = stack_i_minus_1 ->
  Precede stack_i stack_i_minus_1.
Proof.
  induction cards.
- intros.
  inversion H; subst.
  specialize (H0 i H1 H2).
  smack.
- intros.
  smack.
  inversion H; subst.
  
  specialize (H0 i H)
  
  
  
  
Qed.


Lemma lemma1: forall cards ResultStacks i stack_i stack_i_minus_1,
  PatienceSolitaire_Rule cards EmptyStacks ResultStacks ->
  i >= 2 /\ i <= length ResultStacks ->
  nth i ResultStacks default = stack_i ->
  nth (i-1) ResultStacks default = stack_i_minus_1 ->
  Precede stack_i stack_i_minus_1.
Proof.
  induction cards.
- intros.
  smack.
  inversion H; subst.
  smack.
- intros.
  smack.
  
Qed.
*)


(********************************************************************************

  If there is a longer increasing subsequence, by the Pigeonhole Principle, it 
  must contain two sequence elements σ(i) and σ(j) from the same stack, but such 
  elements cannot precede one another.

 ********************************************************************************)

Lemma lemma2:

.



