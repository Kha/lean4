syntax idid := ident ident

syntax "foo" idid : term
#check fun x => `(foo $x)
#check fun x => `(foo $x:idid)
-- extra node
#check fun x => `(foo $x:ident $x:ident)

syntax (unwrapped := true) idid' := ident ident

syntax "foo'" idid' : term
-- no dedicated antiquotation
#check fun x => `(foo' $x $x)
