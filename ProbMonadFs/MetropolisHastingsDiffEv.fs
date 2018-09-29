module MetropalisHastings

open FSharp.Probmonad
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
                return! (if accept then candidate else chainState)
              }
          let next = nextDist.Sample();
                 
          loop (next::newChain) next (n-1)
            
      Pure(loop chain (List.head chain) n)


  let MHPrior (dist:'a Dist) n =
      let initial = [dist.WeightedPrior().Sample()]
      let chain = iterate n (fun () -> dist.WeightedPrior()) initial
      chain.Select (fun iplist -> iplist |> List.map (fun i -> i.Item))

/////////////////////////
module DiffEvolution = 
  let sampleChain proposal (chainState:ItemProb<_>) = dist { 
        let! candidate = proposal()
        let p = min 1. ((candidate:ItemProb<_>).Prob.Div(chainState.Prob).Value)

        let! accept = Primitive( (bernoulliF p).ToSampleDist() )
        return! (if accept then candidate else chainState)
      }

  let inline adjust jitter temperature (next:ItemProb<_>) (next2:ItemProb<_>) (next3:ItemProb<_>) =
      let diff = next2.Item - next3.Item     
      ItemProb(next.Item + temperature * diff + jitter,next.Prob)

  let inline iterate2 jitter temperature n proposal (chain:list<ItemProb<_>>) chain2 chain3 =
      if (n <= 0) then new Pure<_>(chain)
      else            

      let rec loop newChain chainState chainState2 chainState3 n =
          if n = 0 then newChain
          else
          let nextDist = sampleChain proposal chainState 
          let nextDist2 = sampleChain proposal chainState2      
          let nextDist3 = sampleChain proposal chainState3

          let next = nextDist.Sample();
          let next2 = nextDist2.Sample();
          let next3 = nextDist3.Sample();

          let next' = adjust jitter temperature next next2 next3
          let next2' = adjust jitter temperature next2 next next3
          let next3' = adjust jitter temperature next3 next next2
                 
          loop (next'::newChain) next' next2' next3' (n-1)
            
      Pure(loop chain (List.head chain) chain2 chain3 n)

  let inline MHPrior2 jitter temperature (dist:'a Dist) n =
      let initial = [dist.WeightedPrior().Sample()]
    
      let chain = iterate2 jitter temperature n (fun () -> dist.WeightedPrior()) initial (dist.WeightedPrior().Sample()) (dist.WeightedPrior().Sample())
      chain.Select (fun iplist -> iplist |> List.map (fun i -> i.Item))