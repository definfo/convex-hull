# TODO

## Graham's Scan (扫描线)

证明目标

1. 算法得到凸多边形 (DONE)

2. 算法得到的三角形分割构成凸包 (DONE)

3. 算法得到的凸多边形包含所有点 (DONE)

    3.1. 凸包定义等价
    point_in_hull : ⋃ 起始点与各边构成的三角形内部
    point_in_hull_edges : ⋂ 每条边左侧

4. monadlib 程序、C 程序

Instead, prove a refinement to a pure fold, then prove correctness of that fold with a
prefix invariant.

1. Define a pure step/function model (same control flow as step_point):

```rocq
Fixpoint step_fun (p: point) (T: list point) : list point := (* pop until ccw_dec, then
push p *)
...

Definition run_fun (l: list point) :=
  match l with
  | [] => []
  | p1 :: _ => fold_left (fun T p => step_fun p T) l [p1]
  end.
```

2. Prove monadic execution equals pure step:

```
Lemma step_point_spec : forall p T,
  step_point p T tt (step_fun p T).
```

Here do case splits with:

`destruct (ccw_dec a b c) as [Hccw|Hnccw].`

and for absurd branches:

`into_vec_prod. unfold cross_prod, build_vec in *. simpl in *. nia.`

3. Lift to iteration:

```rocq
Lemma prog_list_iter_spec : forall l T,
  prog_list_iter step_point' l tt T tt (fold_left (fun T p => step_fun p T) l T).
```

4. Then:

```rocq
Lemma build_hull_spec : forall l,
  build_hull l [] tt (run_fun l).
```

5. Prove geometric correctness on run_fun by induction on processed prefix (not on rev l):

- invariant shape:

`Inv pref T := is_max_hull' p1 T pref /\ rev_consec_ccw T /\ rev_ccw_list p1 T.`

- step lemma:

`Inv pref T -> sort p1 (pref ++ x :: suf) -> Inv (pref ++ [x]) (step_fun x T).`

Use existing lemmas from Graham_Scan.v (is_max_hull'_pop', sort_ind, sort_gs_* style
lemmas).

6. Final theorem (example):

```rocq
Theorem build_hull_sorted_correct :
  forall p1 l,
    sort p1 l ->
    exists T, build_hull l [] tt T /\ is_max_hull' p1 T l.
```
