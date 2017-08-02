#r @".\bin\Debug\ProbCSharp.dll"
#r @".\bin\Debug\ProbMonadFs.dll"


open ProbCSharp
open FSharp.Probmonad

let z = 
  fdist {let! z = fdist.Join [|bernoulliF 0.5; bernoulliF 0.5|]  
                             (fun x y -> fdist {let! a = x 
                                                let! b = y
                                                return! (a || b) })        
       
         return! z}

let z2 = fdist { let! b1 = bernoulliF 0.5
                 let! b2 = bernoulliF 0.5
                 return! (b1 || b2)}

let zn = fdist { let! b1 = bernoulliF 0.5
                 let! b2 = bernoulliF 0.5
                 let! b3 = bernoulliF 0.5
                 return! (b1 ,b2, b3)}

let b = fdist {
         let! b = bernoulliF 0.5
         return! (if b then "A" else "B")}

b.Explicit |> Seq.toArray
b.ProbOf(fun s -> s = "A")

zn.Explicit |> Seq.toArray
z.Explicit |> Seq.toArray
z2.Explicit |> Seq.toArray

z2.ProbOf(fun x -> x)

