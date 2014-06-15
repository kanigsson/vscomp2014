Require Export ZArith.
Require Export Coq.Arith.Compare_dec.
Require Export Coq.Lists.List.
Require Export X_SparkTactics.

(*****************************************

   Problem 1: Patience Solitaire
   
   Proof by Zhi Zhang @ zhangzhi@ksu.edu

 *****************************************)

Definition Index := nat.
(* for each element, we also record its index, which is its original position in
   input array, and it will be used to track whether one elemnt is preceding another;
*)
Definition Stack := list (Index * nat).
Definition Stacks := list Stack.
Definition EmptyStacks: Stacks := nil.

Definition Index_Of (e: Index * nat) := (fst e).
Definition Value_Of (e: Index * nat) := (snd e).

(**********************************

       Relational Semantics

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
                     To Prove The Lemma1
********************************************************************************)


Require Import Coq.Init.Datatypes.

Definition default: Stack := nil.

Section Auxiliary1.

  Inductive Index_Increasing_True: list (Index * nat) -> Prop :=
    | Index_Inc1:
        Index_Increasing_True nil 
    | Index_Inc2: forall i n,
        Index_Increasing_True ((i, n) :: nil) 
    | Index_Inc3: forall i i' n' ls n,
        i < i' ->
        Index_Increasing_True ((i', n') :: ls) ->
        Index_Increasing_True ((i, n) :: (i', n') :: ls).

  Lemma Index_Increasing_True_Subset: forall a ls,
    Index_Increasing_True (a :: ls) ->
      Index_Increasing_True ls.
  Proof.
    intros.
    inversion H; subst;
    smack.
    constructor.
  Qed.
  
  (* Stack_Indexes_Lt stack i: means all indexes of values in stack are less
     than i; 
  *)
  Inductive Stack_Indexes_Lt: Stack -> nat -> Prop :=
    | S_Less_Than1: forall i' i stack n',
        i' < i ->
        Stack_Indexes_Lt stack i ->
        Stack_Indexes_Lt ((i', n') :: stack) i
    | S_Less_Than2: forall i,
        Stack_Indexes_Lt nil i.

  (* Stacks_Indexes_Lt stack i: means all indexes of values in stacks are less
     than i; 
  *)
  Inductive Stacks_Indexes_Lt: Stacks -> nat -> Prop :=
    | Less_Than1: forall stack i stacks,
        Stack_Indexes_Lt stack i ->
        Stacks_Indexes_Lt stacks i ->
        Stacks_Indexes_Lt (stack :: stacks) i
    | Less_Than2: forall i,
        Stacks_Indexes_Lt nil i.

  Lemma Stack_Indexes_Lt_Subset: forall i' n' ls i,
    Stack_Indexes_Lt ((i', n') :: ls) i ->
    i' < i /\ Stack_Indexes_Lt ls i.
  Proof.
    intros.
    inversion H; subst; smack.
  Qed.

  Lemma Stacks_Indexes_Lt_Subset: forall stack stacks i,
    Stacks_Indexes_Lt (stack :: stacks) i ->
    Stack_Indexes_Lt stack i /\ Stacks_Indexes_Lt stacks i.
  Proof.
    intros.
    inversion H; subst; smack.
  Qed.  


  Lemma Stack_Indexes_Lt_Sn: forall stack i i',
    Stack_Indexes_Lt stack i ->
    i < i' ->
    Stack_Indexes_Lt stack i'.
  Proof.
    intros; induction H; smack.
    constructor; smack.
    constructor.
  Qed.

  Lemma Stacks_Indexes_Lt_Sn: forall stacks i i',
    Stacks_Indexes_Lt stacks i ->
    i < i' ->
    Stacks_Indexes_Lt stacks i'.
  Proof.
    intros; induction H; smack.
    constructor; smack.
    apply Stack_Indexes_Lt_Sn with (i := i); smack.
    constructor.
  Qed.
 

  Lemma Stacks_Indexes_Lt_Trans: forall i n stacks stacks' i',
    Insert_Rule (i, n) stacks stacks' ->
    Stacks_Indexes_Lt stacks i ->
    i < i' ->
    Stacks_Indexes_Lt stacks' i'.
  Proof.
    intros i n stacks stacks' i' H. revert i'.
    remember (i, n).
    induction H. rewrite Heqp.
    - smack.
      inversion H1; subst.
      constructor; smack.
      constructor; smack.
      apply Stack_Indexes_Lt_Sn with (i := i); smack.
      apply Stacks_Indexes_Lt_Sn with (i := i); smack.
    - smack.
      inversion H3; subst.
      specialize (H2 _ H8 H4).
      constructor; smack.
      apply Stack_Indexes_Lt_Sn with (i := i); smack.
    - rewrite Heqp.
      smack.
      constructor; constructor; smack.
      constructor.
  Qed.

  
  (* Precede stack stack': for each element in stack', there is an element
     in stack that precedes it; 
   *)
  Inductive Precede: Stack -> Stack -> Prop :=
    | Precede_NonEmpty: forall stack i' n' stack',
        (exists i n, In (i, n) stack /\ i <= i' /\ n <= n') ->
        Precede stack stack' ->
        Precede stack ((i', n') :: stack')
    | Precede_Empty: forall stack,
        Precede stack nil.


  Lemma In_Supperset(A: Type): forall (a a': A) (ls: list A),
    In a ls ->
      In a (a' :: ls).
  Proof.
    smack.
  Qed.
  
  Lemma Add_Reserved: forall stack stack' a,
    Precede stack stack' ->
      Precede (a :: stack) stack'.
  Proof.    
    intros. revert a.
    induction H; smack.
    constructor.
    exists x, x0.
    specialize (In_Supperset _ (x, x0) (a0, b) stack H1).
    smack.
    apply IHPrecede.
    constructor.
  Qed.


(*
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
*)

  Lemma Precede_Reserved_Help1: forall i n stacks stacks1 i0 n0 stack0,
    Insert_Rule (i, n) stacks stacks1 ->
    i > i0 ->
    n > n0 ->
    Precede ((i0, n0) :: stack0) (nth 0 stacks default) ->
    Precede ((i0, n0) :: stack0) (nth 0 stacks1 default).
  Proof.
    intros.
    inversion H; subst; smack.
  - constructor.
    exists i0, n0; smack.
    auto.
  - constructor.
    exists i0, n0; smack.
    constructor.
  Qed.


  (* if the stacks has "Precede" property, then after inserting an element
     a into the stack according to Patience Solitaire rules, then the result
     stack' should also reserve the "Precede" property.
  *)
  Lemma Precede_Reserved: forall stacks a stacks',
    Insert_Rule a stacks stacks' -> (*  put element a into the stacks according to Patience Solitaire rule *)
    Stacks_Indexes_Lt stacks (Index_Of a) -> (* index of a should be greater than indexes of elements on stacks *)
    (forall j, j >= 1 -> j <= ((length stacks) - 1) -> 
               Precede (nth (j-1) stacks default) (nth j stacks default)) ->  
    (forall i, i >= 1 -> i <= ((length stacks') - 1) ->
               Precede (nth (i - 1) stacks' default) (nth i stacks' default)).
  Proof.
    intros stacks.
    induction stacks; smack.
  - inversion H; smack.
  - inversion H; subst.
    specialize (H1 i).
    destruct i; smack.
    destruct i; smack.
    apply Add_Reserved; auto.

    assert (HZ1: forall j : nat,
       j >= 1 ->
       j <= length stacks - 0 ->
       Precede
         match j - 1 with
         | 0 => (i', n') :: ns
         | S m => nth m stacks default
         end
         match j with
         | 0 => (i', n') :: ns
         | S m => nth m stacks default
         end); auto.

    specialize (H1 i).
    destruct i; smack.
    destruct i; smack.
    inversion H0; subst.
    inversion H6; subst.
    specialize (leb_complete_conv _ _ H10). intros HA1. 
    destruct stacks.
    inversion H11; subst.
    constructor.
    exists i', n'; smack.
    constructor.
    assert(HA2: 1 <= length (s :: stacks) - 0); smack.
    
    assert (HA3: a1 > i'); smack.
    assert (HA4: b > n'); smack.
    assert (HA5: Precede ((i', n') :: ns)  (nth 0 (s :: stacks) default)); smack.
    specialize (Precede_Reserved_Help1 _ _ _ _ _ _ _ H11 HA3 HA4 HA5); auto.

    
    inversion H0; subst.
    specialize (IHstacks _ _ H11 H8).
    remember (S i) as I.
    assert(i = I -1) as HA1. omega.
    rewrite HA1 in *.
    apply IHstacks; smack.
    clear IHstacks.

    assert (HZ2: forall j : nat,
        j >= 1 ->
        j <= length stacks - 0 ->
        Precede
          match j - 1 with
          | 0 => (i', n') :: ns
          | S m => nth m stacks default
          end
          match j with
          | 0 => (i', n') :: ns
          | S m => nth m stacks default
          end); auto.
    specialize (HZ2 j H1).
    destruct j. inversion H1.
    destruct j. simpl in *.
    assert (HA4: 2 >= 1); auto.
    assert (HA5: 2 <= length stacks - 0). omega.
    specialize (HZ1 _ HA4 HA5). 
    auto.
(*    
    assert (HA2: S (S j) <= length stacks - 0). omega.
    specialize (HZ2 HA2).
    simpl in HZ2.
*)
    remember (S (S j)) as J.
    assert (HA2: (S J) >= 1); auto.
    assert (HA3: (S J) <= length stacks - 0). omega.
    specialize (HZ1 _ HA2 HA3).
    simpl in HZ1.
    destruct J.
    inversion HeqJ.
    assert (HA4: S J - 1 = J). omega.
    rewrite HA4.
    simpl in HZ1. 
    auto.
  Qed.

End Auxiliary1.



Lemma lemma1_helper: forall cards i card InitialStacks ResultStacks,
  PatienceSolitaire_Rule ((i, card) :: cards) InitialStacks ResultStacks ->
  Index_Increasing_True ((i, card) :: cards) ->
  Stacks_Indexes_Lt InitialStacks i ->
  (* requirement for the initial stack *)
  (forall j, j >= 1 -> j <= ((length InitialStacks) - 1) -> 
             Precede (nth (j-1) InitialStacks default) (nth j InitialStacks default)) ->
  (forall i, i >= 1 -> 
             i <= (length ResultStacks - 1) ->
             Precede (nth (i-1) ResultStacks default) (nth i ResultStacks default)).
Proof.
  induction cards.
- intros.
  inversion H; subst.
  inversion H10; subst.
  specialize (Precede_Reserved _ _ _ H7 H1 H2).
  smack.
- intros.
  inversion H; subst.
  specialize (Index_Increasing_True_Subset _ _ H0); smack.
  destruct a.
  inversion H0; subst.
  specialize (Stacks_Indexes_Lt_Trans _ _ _ _ _ H7 H1 H9).
  intros HZ1.
  specialize (IHcards _ _ _ _ H10 H5 HZ1).
  apply IHcards; clear IHcards; smack.
  specialize (Precede_Reserved _ _ _ H7 H1 H2); smack.
Qed.


(********************************************************************************
   < Lemma 1 >
   
   To each element in stack i+ 1, there is an element in stack i that precedes it, 
   so that by chaining these elements, we can construct an increasing subsequence 
   of length n;
 ********************************************************************************)


Lemma lemma1: forall cards ResultStacks,
  PatienceSolitaire_Rule cards EmptyStacks ResultStacks ->
  Index_Increasing_True cards ->
  (forall i, i >= 1 -> 
             i <= (length ResultStacks - 1) ->
             Precede (nth (i-1) ResultStacks default) (nth i ResultStacks default)).
Proof.
  intros.
  destruct cards.
- inversion H; subst.
  smack.
- destruct p.
  apply lemma1_helper with (cards := cards) (i := i0) (card := n) (InitialStacks := EmptyStacks);
  smack.
  constructor.
Qed.



(********************************************************************************
                     To Prove The Lemma2
********************************************************************************)

Section Auxiliary2.
  (* this will be used to show that: for each stack of the resulting stacks 
     produced by Patience Solitaire game, its indexes are in decreasing order,
     which is used to prove the lemma2 that: it's impossible to contain two 
     sequence elements σ(i) and σ(j) from the same stack and they precede one 
     another;
  *)
  Inductive Index_Decreasing_True: list (Index * nat) -> Prop :=
    | Index_Dec1:
        Index_Decreasing_True nil 
    | Index_Dec2: forall i n,
        Index_Decreasing_True ((i, n) :: nil) 
    | Index_Dec3: forall i i' n' ls n,
        i > i' ->
        Index_Decreasing_True ((i', n') :: ls) ->
        Index_Decreasing_True ((i, n) :: (i', n') :: ls).
  
  Lemma Index_Decreasing_Reserved: forall stacks a stacks',
    Insert_Rule a stacks stacks' -> (*  put element a into the stacks according to Patience Solitaire rule *)
    Stacks_Indexes_Lt stacks (Index_Of a) -> (* index of a should be greater than indexes of elements on stacks *)
    (forall j, j >= 0 -> 
               j + 1 <= (length stacks) -> 
               Index_Decreasing_True (nth j stacks default)) ->  
    (forall i, i >= 0 -> 
               i + 1 <= (length stacks') ->
               Index_Decreasing_True (nth i stacks' default)).
Proof.
  intros stacks.
  induction stacks; smack.
- inversion H; smack.
  assert (i = 0); smack.
  constructor.
- inversion H; subst.
  specialize (H1 i);
  destruct i; smack.
  inversion H0; subst. inversion H6; subst.
  constructor; smack.
  
  assert (HZ1: forall j : nat,
       j >= 0 ->
       j + 1 <= S (length stacks) ->
       Index_Decreasing_True
         match j with
         | 0 => (i', n') :: ns
         | S m => nth m stacks default
         end); auto.
  specialize (H1 i);
  destruct i; smack.
  specialize (Stacks_Indexes_Lt_Subset _ _ _ H0); smack.
  specialize (IHstacks (a1, b) stacks'0 H11 H6).
  apply IHstacks; smack.
  specialize (HZ1 (j + 1)).
  assert(HA1: j + 1 >= 0). smack.
  assert(HA2: j + 1 + 1 <= S (length stacks)). smack.
  specialize (HZ1 HA1 HA2).
  assert (HA3: j + 1 = S j). smack.
  rewrite HA3 in HZ1. auto.
Qed.
 
End Auxiliary2.



Lemma lemma2_helper: forall cards i card InitialStacks ResultStacks,
  PatienceSolitaire_Rule ((i, card) :: cards) InitialStacks ResultStacks ->
  Index_Increasing_True ((i, card) :: cards) ->
  Stacks_Indexes_Lt InitialStacks i ->
  (* requirement for the initial stack *)
  (forall j, j >= 0 -> 
             j + 1 <= (length InitialStacks) -> (* j <= length InitialStacks -1, which will not work when InitialStacks is emtpy *)
             Index_Decreasing_True (nth j InitialStacks default)) ->
  (forall i, i >= 0 -> 
             i + 1 <= length ResultStacks ->
             Index_Decreasing_True (nth i ResultStacks default)).
Proof.
  induction cards.
- intros.
  inversion H; subst.
  inversion H10; subst.
  specialize (Index_Decreasing_Reserved _ _ _ H7 H1 H2).
  smack.
- intros.
  inversion H; subst.
  specialize (Index_Increasing_True_Subset _ _ H0); smack.
  destruct a.
  inversion H0; subst.
  specialize (Stacks_Indexes_Lt_Trans _ _ _ _ _ H7 H1 H9).
  intros HZ1.
  specialize (IHcards _ _ _ _ H10 H5 HZ1).
  apply IHcards; clear IHcards; smack.
  specialize (Index_Decreasing_Reserved _ _ _ H7 H1 H2); smack.
Qed.


(********************************************************************************
  <Lemma 2>
  
  If there is a longer increasing subsequence, by the Pigeonhole Principle, it 
  must contain two sequence elements σ(i) and σ(j) from the same stack, but such 
  elements cannot precede one another.

  the following lemma2 shows that: for each stack of the resulting ResultStacks 
  produced by Patience Solitaire game, its indexes are in decreasing order, which 
  demonstrates that: it's impossible to contain two sequence elements σ(i) and σ(j) 
  from the same stack and they precede one another;

 ********************************************************************************)

Lemma lemma2: forall cards ResultStacks,
  PatienceSolitaire_Rule cards EmptyStacks ResultStacks ->
  Index_Increasing_True cards ->
  (forall i, i >= 0 -> 
             i + 1 <= length ResultStacks -> (* i <= length ResultStacks -1, which will not work when ResultStacks is emtpy *)
             Index_Decreasing_True (nth i ResultStacks default)).
Proof.
  intros.
  destruct cards.
- inversion H; subst.
  smack.
- destruct p.
  apply lemma2_helper with (cards := cards) (i := i0) (card := n) (InitialStacks := EmptyStacks);
  smack.
  constructor.  
Qed.

