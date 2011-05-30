

main gi fi xi = map gi (map fi xi)

map f x = case x of
    Nil -> Nil
    Cons y ys -> Cons (f y) (map f ys)
