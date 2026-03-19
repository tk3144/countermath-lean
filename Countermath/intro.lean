/-
Some introductory lean...
-/



section Example1
theorem T (b c d : Nat) (h1 : a = b) (h2 : b = c + 1) (h3 : c = d) (h4 : e = 1 + d) : a = e :=
  calc
    a = b := h1
    b = c + 1 := h2
    c + 1 = d + 1 := congrArg Nat.succ h3
    d + 1 = 1 + d := Nat.add_comm d 1
    1 + d = e := Eq.symm h4

#check T
end Example1
