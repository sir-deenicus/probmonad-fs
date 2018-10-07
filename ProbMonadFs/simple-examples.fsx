#r @"bin\Debug\prelude.dll"
#r @"bin\Debug\MathNet.Numerics.dll"
#r @"bin\Debug\ProbCSharp.dll"
#r @"bin\Debug\ProbMonadFs.dll"

open Probmonad
open Probmonad.Core

let pr = 
    dist {
      let! m = normal 0. 1.
      let! s = gamma 1. 1. 
      return (m,s)
    }

[5.; 6.; 20.] |> computePosterior (fun (m,s) x -> pdf (normal m s) x) pr