/-
Copyright 2026 Henrik Tscherny, Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

/-!
**The files in this directory are in an early stage of development. There is directory level documentation available in the CoreChase.lean file that describes what is going to happen here.**
-/

public section

/-

  l = [x1, x2, x3, x4]

  y1 = f init x1
  y2 = f y1 x2
  y3 = f y2 x3

  foldl_save_hist l init f = [init, (f init x1), (f (f init x1) x2), (f (f (f init x1) x2) x3)]

  foldl_save_hist l init f = [init, y1, y2, y3]

-/

-- foldl_save_hist variant for function returning options, if none is returned by f the argument is not applied and the previous element which was some is returned
def foldl_save_hist_opt (l : List α) (init_elem : β) (f : β → α → Option β) : List β :=
  let (_, history) :=
    l.foldl
      (fun (state, hist) t =>
        match (f state t) with
          | some s' => (s', hist.concat s')
          | none    => (state, hist)
        )
      (init_elem, [init_elem])
  history

def foldl_save_hist_opt_nodup [DecidableEq β] (l : List α) (init_elem : β) (f : β → α → Option β) : List β :=
  let (_, history) :=
    l.foldl
      (fun (state, history) t =>
        let next := (f state t).getD state
        if next = state then
          (state, history)
        else
          (next, history.concat next))
      (init_elem, [init_elem])
  history

def foldl_save_hist_opt_nodup_trace [DecidableEq β](l : List α) (init : β) (f : β → α → Option β) : List (β × Option α) :=
  (l.foldl
    (fun
      | (state, hist), o =>
        if (f state o).getD state = state then
          (state, hist)
        else
          ((f state o).getD state,
           hist ++ [((f state o).getD state, some o)]))
    (init, [(init, none)])).2


def test_fun (a b : Nat) : Option (Nat) :=
    if (a > b) then a - b else none

#eval foldl_save_hist_opt [5, 20, 20, 1, 10, 5, 0, 1] 20 test_fun

#eval foldl_save_hist_opt_nodup [10, 5, 8, 3] 20 test_fun

#eval foldl_save_hist_opt_nodup_trace [5, 20, 20, 1, 10, 5, 0, 1] 20 test_fun

theorem foldl_save_hist_opt_nodup_head_eq [DecidableEq β] (l : List α) (init_elem : β) (f : β → α → Option β) :
(foldl_save_hist_opt_nodup l init_elem f).head? = some init_elem := by
  unfold foldl_save_hist_opt_nodup
  have h : ∀ (l : List α) (state : β) (hist : List β),
    hist.head? = some init_elem → (l.foldl (fun (state, hist) t =>
      let next := (f state t).getD state
      if next = state then
        (state, hist)
      else
        (next, hist.concat next))
      (state, hist)).snd.head? = some init_elem := by
        intro l
        induction l with
          | nil =>
            grind
          | cons hd tl ih =>
            grind

  exact h l init_elem [init_elem] rfl

theorem foldl_save_hist_opt_nodup_trace_adjacent_ne [DecidableEq β] (l : List α) (init : β) (f : β → α → Option β) (n : Nat) (h : n + 1 < (foldl_save_hist_opt_nodup_trace l init f).length) :
  (foldl_save_hist_opt_nodup_trace l init f)[n] ≠ (foldl_save_hist_opt_nodup_trace l init f)[n+1] := by
    intro contra
    let hist := foldl_save_hist_opt_nodup_trace l init f
    have hist_eq : hist[n] = hist[n+1] := contra

    have hstep :
      ∃ (state next : β) (o : Option α),
        hist[n] = (state, o) ∧
        hist[n+1] = (next, o) ∧
        next ≠ state := by

      have : ∃ (state next : β) (o : Option α),
        (foldl_save_hist_opt_nodup_trace l init f)[n]'(Nat.lt_of_succ_lt h) = (state, o) ∧
        (foldl_save_hist_opt_nodup_trace l init f)[n+1]'(by exact Nat.lt_of_succ_le h) = (next, o) ∧
        next ≠ state := by
          induction l generalizing n with
          | nil =>
            exists init
          | cons hd tl ih =>
            sorry
      exact this
    grind

