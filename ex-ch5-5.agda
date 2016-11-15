

bst-remove-min : ∀ {l u : A} → bst l u → bst l u
bst-remove-min (bst-leaf x) = bst-leaf x
bst-remove-min (bst-node d (bst-leaf l) (bst-leaf r) lb rb) = bst-leaf (≤A-trans (≤A-trans (≤A-trans lb l) r) rb)
bst-remove-min (bst-node d (bst-leaf l) (bst-node d₁ lbst rbst lb' rb') lb rb) = bst-node d₁ lbst rbst (≤A-trans (≤A-trans lb l) lb') (≤A-trans rb' rb)
bst-remove-min (bst-node d lnode rbst lb rb) = bst-node d (bst-remove-min lnode) rbst lb rb

bst-remove-max : ∀ {l u : A} → bst l u → bst l u
bst-remove-max (bst-leaf x) = bst-leaf x
bst-remove-max (bst-node d (bst-leaf x) (bst-leaf x₁) lb rb) = (bst-leaf (≤A-trans (≤A-trans (≤A-trans lb x) x₁) rb))
bst-remove-max (bst-node d (bst-node d₁ lbst rbst lb' rb') (bst-leaf x₂) lb rb) = bst-node d₁ lbst rbst (≤A-trans lb lb') (≤A-trans (≤A-trans rb' x₂) rb)
bst-remove-max (bst-node d lbst rnode lb rb) = bst-node d lbst (bst-remove-max rnode) lb rb

bst-get-min : ∀ {l u : A} → bst l u → maybe A
bst-get-min (bst-leaf x) = nothing
bst-get-min (bst-node d (bst-leaf x) rbst lb rb) = just d
bst-get-min (bst-node d (bst-node d₁ lbst' rbst' lb' rb') rbst lb rb) = bst-get-min lbst'

bst-is-node : ∀ {l u} → (bst l u) → bool
bst-is-node (bst-leaf x) = ff
bst-is-node (bst-node d bst bst₁ x x₁) = tt

bst-min-of-node-not-nothing : ∀ { l u : A} → (b : bst l u) → bst-get-min b ≡ nothing → bst-is-node b ≡ ff
bst-min-of-node-not-nothing (bst-leaf x) p = refl
bst-min-of-node-not-nothing (bst-node d b b₁ x x₁) ()

bst-remove : ∀ {l u : A}(d : A) → bst l u → bst l u
bst-remove d (bst-leaf x) = bst-leaf x
bst-remove d (bst-node d' lbst rbst lb rb) with keep (d ≤A d')
bst-remove d (bst-node d' lbst rbst lb rb) | tt , p with keep (d' ≤A d)
bst-remove d (bst-node d' (bst-leaf x) (bst-leaf x₁) lb rb) | tt , b₁ | tt , b = bst-leaf (≤A-trans (≤A-trans (≤A-trans lb x) x₁) rb) -- d=d'; two leaves => replace with leaf
bst-remove d (bst-node d' (bst-leaf x) (bst-node d₁ lbst rbst lb' rb') lb rb) | tt , b₁ | tt , b = bst-node d₁ lbst rbst (≤A-trans (≤A-trans lb x) lb') (≤A-trans rb' rb) -- d=d'; leaf-node => replace with right branch
bst-remove d (bst-node d' (bst-node d₁ lbst rbst lb' rb') (bst-leaf x₂) lb rb) | tt , b₁ | tt , b = bst-node d₁ lbst rbst (≤A-trans lb lb') (≤A-trans (≤A-trans rb' x₂) rb) --d=d'; node-leaf => replace with left branch
bst-remove d (bst-node d' lnode rnode lb rb) | tt , b₁ | tt , b with keep(bst-get-min rnode)
bst-remove d (bst-node d' lnode rnode lb rb) | tt , b₂ | tt , b₁ | just x , b = {!!} --{!bst-node (bst-get-min rnode ) lnode (bst-remove-min rnode) ? ?!}
bst-remove d (bst-node d' lnode rnode lb rb) | tt , b₂ | tt , b₁ | nothing , b = bst-node d' lnode rnode lb rb -- shouldn't occur?
bst-remove d (bst-node d' lbst rbst lb rb) | tt , b₁ | ff , b = bst-node d' (bst-remove d lbst) rbst lb rb -- d<d' remove in left branch
bst-remove d (bst-node d' lbst rbst lb rb) | ff , p = bst-node d' lbst (bst-remove d rbst) lb rb -- d>d' is larger, remove in right branch
