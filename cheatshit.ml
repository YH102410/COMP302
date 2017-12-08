let rec map_tree_k (f : 'a -> 'b) (t : 'a tree) (k : 'b tree -> 'c) : 'c =
  match t with
  | Leaf -> k Leaf
  | Node(l, x, r) -> map_tree_k f l (fun l' -> map_tree_k f r (fun r' -> k (Node (l', f x, r’))))
let rec tree_fold f e t = match t with
  | Leaf -> e
  | Node (l, c, r) -> f (c, tree_fold f e l, tree_fold f e r)
let size    tr = tree_fold (fun (c, l, r) -> 1 + l + r) 1 trc
let reflect tr = tree_fold (fun (c, l, r) -> Node (r, c, l)) Leaf tr
let inorder tr = tree_fold (fun (c, l, r) -> l @ [c] @ r) [] tr
let change_top coins amt =
  try 
    let c = change coins amt in
    print_string ("Return the following change: " ^ listToString c ^ "\n")
  with Change -> print_string ("Sorry, I cannot give change\n")
let rec cchange (coins: int list) (amt:int) (fc: unit -> int list) = 
  try change coins amt with Change -> fc ()
let cchange_top coins amt = 
  try 
    let c = cchange coins amt (fun () -> raise Change) in
    print_string ("Return the following change: " ^ listToString c ^ "\n")
  with Change -> print_string ("Sorry, I cannot give change\n")
type 'a str = {hd: 'a  ; tl : ('a str) susp} 
let rec str_ones = {hd = 1 ; tl = Susp (fun () -> str_ones)}
let rec numsFrom n = 
  {hd = n ;
   tl = Susp (fun () -> numsFrom (n+1))}
let nats = numsFrom 0
let rec take_str n s = match n with 
  | 0 -> []
  | n -> s.hd :: take_str (n-1) (force s.tl)
let rec zip f s1 s2 =  {hd = f s1.hd s2.hd ; tl = delay (fun () -> zip f (force s1.tl) (force s2.tl)) }
let rec add_str s1 s2 = zip (fun x1 x2 -> x1 + x2) s1 s2
let rec constant c = {hd = c; tl = delay (fun () -> constant c) }
let rec psums s = let rec psums' s' sum' = let sum = s'.hd + sum' in
                    {hd = sum  ; tl = delay (fun() -> psums' (force s'.tl) sum)} in
  psums' s 0
type action = Open | Close
exception Error of string
let make_lock  = fun lock action -> match action with
  | Open -> if !lock = Close then lock := Open else raise (Error "Already opened")
  | Close -> if !lock = Open then lock := Close else raise (Error "Already closed")
let with_lock = make_lock (ref Open)
let rec size t = match t with 
  | Leaf -> 0 
  | Node (l, x, r) -> x + size l + size r
let rec size_acc t acc = match t with 
  | Leaf -> acc
  | Node (l, x, r) -> size_acc l (x + size_acc  r acc)  
(*Binding:
let <name> = <expression 1> in <expression 2>;
In this expression, the binding of <name> and <expression 1> is removed from the stack after evaluating the whole function!
=> the scope of the variable <name> ends after <expression 2>
The local variable may overshadow a global variable of same name temporarily in it's scope
Define a type:
The oerder does not matter and each element should begin with acapital letter
Elements of a given type is defined by the constructors
Curry and Uncurry:
the function is to change the order of input, not the function*)
let curry f = (fun f x y -> f (x, y) )
type: curry: (('a * 'b) -> 'c) -> ('a -> 'b -> 'c)(*
the function we take as input is a function take in a tuple (x, y), and in this function we let it become a function that can take x and y separatly.*)
let uncurry f = (fun f (x, y) -> f x y )
type: uncurry: ('a -> 'b -> 'c -> (('a -> 'b) -> 'c )
(*function types are right associated: 'a -> 'b -> 'c = 'a -> ('b -'c) 
functino appliaction is left associated: f a b = (f a) b
=> (f a): still a function: ('b -> 'c): b has type 'b and the product has type 'c*)
let swap f = (fun f (x,y) -> f (y, x)) 
type: swap: ('a * 'b -> c) -> ('b * 'a -> 'c)
(*partial evaluation and staged computation:*)
let funckyPlus x y = x * x + y 
(*and we want to substitute y later: let plus9 = funckyPlus 3 -> plus9 : int -> int
plus9 = 3 * 3 + y <= the function will not compute the inside
how to fix y: plus3 = fun x -> funckyPlus x 3 *)
let test (x:int) = let z = horribleComputation x in z + y (*will compute z every time*)
let testCorrest (x:int) = let z = horribleComputation x in (fun y -> y + z) 
(*in this function we factor out z and the value of z will be stored after computing*)
(*the reference expression: _ = r := 3; has type unit, because the value of the expression is discard by the binding.*)
exp1; exp2  (*a shorthand of the let _ = exp1 in exp2 expression = only used in ref*)
let {content = x} = s;; 
val x : int = 0
y = !r;;
(*if not ... then => same as !... in C
Teke care of the expression about ref: := change the value in the cell; ! take the value; = connect to the same cell, or compare value; 
When to use ref: the state must be maintained*)
let counter = ref 0
let newName () = 
  (counter := ! counter + 1;
   "a"^string_of_int (!counter))
(*In this function want to generate newName, and need a global variable to track the what newName we have generated so far (only when you need to track something that you need a gobal ref varaible to use later in program
If it's not ref or global, the new binding/ref discard after the scope.*)
let counter = ref 0 in
let tick () = counter := !counter + 1; !counter in
let reset () = (counter := 0 ) in 
(tick, reset)
(*The 2 functions tick and reset share a private variable counter that is bound to a reference cell containing the current value of a shared counter.*)
type counter_object = {tick : unit -> int ; reset : unit -> unit}
let newCounter () = 
let counter = ref 0 in 
{ tick = (fun () -> counter := !counter +1l !counter; (*Using this expression, you can define the object of type counter_object*)
  reset = fun () -> counter := 0 }
(*Use*)
let c1 = newCounter();;
c1.tick();;
=> -: int = 1
c1.reset();;
=> -: unit () (*the reset function returns a unit and tick funciton returns the value *)
(*Other Common Mutable Structure*)
type nameT = {name1 : type; name2 : type ; ... ; mutable nameM : type } 
(*The mutable type variable can be updated, and others are only regular variable
update (not only the mutable type, the other variables are updated the same way):*)
let nameV = {name1 = ...; ...; nameM = ...}
nameV.nameM <- ...(*new data*)
(*Exception*)
exception exceptionName
(*set an exception first and use later when needed*)
let rec find t k = match t with 
  | Empty -> raise NotFound
  | Node (l , (k', d), r) -> 
      if k = k' then d
      else try find l k with NotFound -> find r k 
(*The tree construstor not present and*)
(*Modules*)
module Name = 
  struct 
    type typeName = aType (*Type: type stack = int list*)
    let funcName  var = ...
    let empty () : stack = [] (*-> : stack is the return type*)
end
module STACK = (*super type*)
  sig stack (*sub type*)
  val name : unit -> stack 
end 
(*A module (strct) amy contain more than the type (sig): something we do not want to expose
  module provide a more general type(sig: struct -> bool; struct: 'a list -> bool)
  the order in struct don't need to be the same as sig
  -avoid over-specification: A data type may be provided where a type is required; a valu econstructor may be provided where s value is required
To keep element abstract: create a type e1, and generalize the type with e1*)
module IntStack : (STACK with type e1 = int) = 
  struct 
    type e1 = int 
    type stack = int list ... end
(*Then e1 in sig are all becomes int*)
(*Abbreviation*) module IS = IntStack;
(*open (keyword)*)
open structName
(*Will incorporate and expose the body of the structure structName into the current emvironment, without qualification
 problem: by using open, we are erasing any structure and name space separation
 => when open 2 structures have a component of the same name; the second one will overshadow the first one
 What's opened? => the functions, types, and the help functions which you may not want to show; Example:*)
module Float = 
 struct
  type t = float
  let unit = 1.0
  let prod = ( *. )
end;;
module Euro = (float : CURRENCY)
(*Didn't say float matches type CURRENCY(not shown; a sig) => reuse the type CURRENCY fro different currencies
 module Euro =>  hide the fact that we use float as the type of CURRENCY; How to use:*)
let euro = Euro.prod x Euro.unit;;
val euro : float -> Euro.t = <fun> (*The type of Euro becomes Euro.t, work on type Euro.t only: you cannot add Euro 10. with CAD 10.0 though they are all floats*)
let x = Euro.plus (euro 10.0) (euro 20.0);;
val x : Euro.t = <abstr>
(*Bank and Client example:*)
module type CLIENT = 
sig 
  type t 
  type currency 
  ... end;;
module type BANK = 
sig 
  include CLIENT 
  val create : unit -> t
end;;
(*the keyword INCLUDE: include all the declaration of CLIENT into bank, the sig of BANK inherits all declaration of CLIENT
 There is no overloading, if you redefine a name in CLIENT, OCaml will overshadow the one defeined in CLIENT*)
module Old_Bank (M: CURRENCY): (BANK with type currency = M.t(* and type t = ... : keyword AND*))
(*In this expression: M is the Abbreviation of CURRENCY, and we can get a branch of Bank using Euro, CAD...*)
module Post - Old_Bank (Euro);; (*Define a Bank with CURRENCY of Euro, match the define of bank*)
module Post_Client :(CLIENT with type currency = Post.currency and type t = Post.t) = Post;;
(*A client has a Post account and rely on the information hiding, Post provides a way to create a new account, but Post_Client.create does not exist*)
(*A advanced Bank:*)
module Bank (M: CURRENCY) : (BANK with type currency = M.t)
struct
  let zero = M.prod 0.0 M.unit
  and neg = M.prod (-1.0)
  type t = int 
  type currency = M.t
  type account = {number : int ; mutable balance : currency }
(*to bind a value to a variable in an account*)
c.balance <- M.plus c.balance x
(*You can use Old_Bank and Bank to have bank in different type, though they are from same sig, they are implemented differently, and the user may not be able to notice the difference but the typechecker will*)
(*Continuation: the initial continuation is always identity function, means you do nothing to the result; app axampl:*)
app [1;2] [3;4] ((((fun r -> c (h::t))the continuation for (h::t))))
=> app [2] [3;4] (fun r1 -> (fun r -> r) (1::r1))
=> app [] [3;4] (fun r2 -> (fun r1 -> (fun (r -> r) [1::r1])) (2::r2))
=> (fun r2 -> (fun r -> r) (1::r1)) (2::[3;4]))
=> (fun r -> r) (1::2::[3;4]) 
(*If you do tail recursive to find element in a tree, you have to pass the value back to the top, but if you use continuation, you can return it right after finding it
regular expression matching:
singleton: matching a specific character; alternation: choice between 2
concentation: succession of patterns; Iteration: indefinite reprtition of patterns
·: match anything except newline; *: repeat or none; +: repeat at least once
?: once or none; */+/? with a ?( *?)will match the least: a string with "abb": ab*? => a; a* => abb *)
(* LAZY: set up *)
type 'a susp = Susp of (unit -> 'a)
let force (Susp f) = f()
type 'a list = Nil | Cons of 'a * 'a list
type 'a str = {hd: 'a; tl: ('a str) susp}
