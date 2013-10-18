type name = string

type kind = Kstar 
          | Kpi of name * typ * kind
and typ = Tvar of name
        | Tall of name * typ * typ
        | Tapp of typ * term

and term = Mvar of name
         | Mapp of term * term
         | Mabs of name * typ * term

let dummy = "_"
let karr (x,y) = Kpi (dummy,x,y)
let tarr (x,y) = Tall (dummy,x,y)

let k0 = Kstar
let t0 = Tvar "0"
let k1 = karr (t0,k0)
let m1 = Mabs ("x",t0,Mvar "x")
