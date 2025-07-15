module Payrolls

open System.Runtime.CompilerServices

[<IsReadOnly; Struct>]
type Payroll(month: int, amount: decimal) =
    member this.Month = month
    member this.Amount = amount

    static member Calculate(month: int, yearAmount: decimal) =
        if month < 1 || month > 12 then invalidOp "Parameter month should be in interval 1..12"
        if yearAmount <= 0M then invalidOp "Parameter yearAmount should be positive"

        let month = uint month
        let yearAmount = uint (yearAmount * 100M)
        Coq.make_payrolls month yearAmount
        |> List.sortBy fst
        |> List.map (fun (month, amount) -> new Payroll(int month, decimal amount / 100M))
        |> List.toArray
