(* emacs with tuareg, merlin, utop *)

type num = int

type exp =
| Num of num
| Plus of exp * exp

let is_val (e : exp) : bool =
  match e with
  | Num n -> true
  | _ -> false

let rec eval (e : exp) : exp = 
  match e with
  | Num n -> Num n
  | Plus (e1,e2) ->
     begin match eval e1, eval e2 with
     | Num n1, Num n2 -> let n = Num (n1 + n2) in n
     | _ -> invalid_arg "plus"
     end
  | _ -> failwith "unimp: eval"

let _ =
  let num2 = Num 2 in
  let _ = assert (num2 = eval num2) in
  let _ = assert (Num 4 = eval (Plus(num2,num2))) in
  print_endline "hello"
