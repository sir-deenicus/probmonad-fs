namespace Probmonad

open Probmonad.Core
open ProbCSharp     

module SimpleMCMC =
  let iterate n proposal (chain:list<ItemProb<_>>) =
      if (n <= 0) then new Pure<_>(chain)
      else            

      let rec loop newChain (chainState:ItemProb<_>) n =
          if n = 0 then newChain
          else
          let nextDist = 
              dist { 
                let! candidate = proposal()
                let p = min 1. ((candidate:ItemProb<_>).Prob.Div(chainState.Prob).Value)

                let! accept = Primitive( (bernoulliF p).ToSampleDist() )
                return (if accept then candidate else chainState)
              }
          let next = nextDist.Sample();
                 
          loop (next::newChain) next (n-1)
            
      Pure(loop chain (List.head chain) n)

  let MHPrior (dist:'a Dist) n =
      let initial = [dist.WeightedPrior().Sample()]
      let chain = iterate n (fun () -> dist.WeightedPrior()) initial
      chain.Select (fun iplist -> iplist |> List.map (fun i -> i.Item))

/////////////////////////
