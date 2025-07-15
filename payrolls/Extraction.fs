module Coq

(** val make_payrolls_until_november :
    uint -> uint -> (uint * uint) list -> (uint * uint) list **)

let rec make_payrolls_until_november count amount result =
  (fun zero succ n -> if n = 0u then zero () else succ (n - 1u))
    (fun _ -> result)
    (fun count' ->
    make_payrolls_until_november count' amount
      ((((-) 12u count) , amount)::result))
    count

(** val make_payrolls_until_december :
    uint -> uint -> uint -> (uint * uint) list **)

let make_payrolls_until_december count month_amount december_amount =
  (12u , december_amount)::(make_payrolls_until_november
                             ((-) count ((+) 1u 0u)) month_amount [])

(** val make_partial_payrolls : uint -> uint -> (uint * uint) list **)

let make_partial_payrolls count partial_amount =
  let month_amount = (/) partial_amount count in
  let december_amount = (+) month_amount ((%) partial_amount count) in
  make_payrolls_until_december count month_amount december_amount

(** val make_payrolls : uint -> uint -> (uint * uint) list **)

let make_payrolls month year_amount =
  let count = (-) ((+) 1u 12u) month in
  let partial_amount = (/) ((*) count year_amount) 12u in
  make_partial_payrolls count partial_amount
