#eval do
  t1 ← IO.asTask $ Nat.forM 10 fun _ => IO.println "hi";
  t2 ← IO.asTask $ Nat.forM 10 fun _ => IO.println "ho";
  IO.ofExcept t2.get;
  IO.ofExcept t1.get;
  pure ()
