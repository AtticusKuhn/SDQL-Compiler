# SDQL optimisations
Vertical Loop Fusion:

before: let y=sum(<x,x_v> in e1){f1(x)->x_v} in sum(<x,x_v> in y){f2(x)->x_v}
after: sum(<x,x_v> in e1) { f2(f1(x)) -> x_v }

before: let y=sum(<x,x_v> in e1){x->f1(x_v)} in sum(<x,x_v> in y){x->f2(x_v)}
after: sum(<x,x_v> in e1) { x -> f2(f1(x_v)) }

Horizontal Loop Fusion:

before: y1=sum(x in e1) f1(x) in let y2=sum(x in e1) f2(x) in f3(y1, y2)
after: let tmp = sum(x in e1) <y1 = f1(x), y2 = f2(x)> in f3(tmp.y1, tmp.y2)

Loop Factorization:

before: sum(x in e1) (e2 * f(x))
after: e2 * (sum(x in e1) f(x))

before: sum(x in e1) (f(x) * e2)
after: (sum(x in e1) f(x)) * e2

Loop-Invariant Code Motion:

before: sum(x in e1) let y = e2 in f(x, y)
after: let y = e2 in sum(x in e1) f(x, y)

Loop Memoization:

before: sum(x in e1) if(p(x) == e2) then g(x, e3) 
after: let tmp = sum(<k,v> in e1) {p(x) -> {k -> v}} in sum(x in tmp(e2)) g(x, e3)

before: sum(x in e1) if(p(x) == e2) then f(x)
after: let tmp = sum(x in e1) {p(x) -> f(x)} in tmp(e2)
