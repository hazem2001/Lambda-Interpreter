Object subclass: Lambda [
    | expr map |

    Lambda class >> new: exp [
        | r |
        r := super new.
        r init: exp.

        ^r
    ]

    init: exp [
        expr := exp dup. "HUGE ISSUE"
        map := Dictionary new.
    ]

    "var is a string. exp is lambdaExpr"
    substitute: var for: exp [
        expr ifVar: [
            var = (expr name) ifTrue: [
                expr := exp dup.
            ]
        ]
        ifAbs: [
            | varAbs newVarAbs bodyAbs freeVarMap hadKey|
            varAbs := (expr var).
            bodyAbs := (expr body) dup.

            (varAbs = var) ifFalse: [
                freeVarMap := exp freeVars: (Dictionary new).
                hadKey := freeVarMap includesKey: varAbs.

                hadKey ifTrue: [
                    newVarAbs := varAbs , (self hash asString).
                    bodyAbs := Lambda new: (bodyAbs).
                    bodyAbs substitute: varAbs for: (LambdaVar withName: newVarAbs).
                    bodyAbs substitute: var for: exp.

                    expr init: newVarAbs body: (bodyAbs getExp).
                ] ifFalse: [
                    bodyAbs := Lambda new: (bodyAbs).
                    bodyAbs substitute: var for: exp.

                    expr init: varAbs body: (bodyAbs getExp).
                ]
            ]
        ]
        ifApp: [
            | rat rad |

            rat := Lambda new: (expr rator).
            rat substitute: var for: exp.

            rad := Lambda new: (expr rand).
            rad substitute: var for: exp.

            expr init: (rat getExp) rand: (rad getExp).
        ].

        ^expr.
    ]
  
    addOne: mp [
        mp keysAndValuesDo: [:key :value |
            mp at: key put: (value + 1). 
        ].
    ]

    setMap: mp [
        map := mp copy.
    ]

    getExp [
        ^expr
    ]

    toDeBruijn [
        
        expr ifVar: [
            | hadKey |
            hadKey := map includesKey: (expr name).

            hadKey ifTrue: [
                expr init: (map at: (expr name)).
            ] 
        ]
        ifAbs: [
            | var body |
            
            self addOne: map.
            map at: (expr var) put: 1.

            body := Lambda new: (expr body).
            body setMap: map.
            body toDeBruijn.

            expr init: nil body: (body getExp).
        ]
        ifApp: [
            | rat rad |

            rat := Lambda new: (expr rator).
            rat setMap: map.
            rat toDeBruijn.

            rad := Lambda new: (expr rand).
            rad setMap: map.
            rad toDeBruijn.
        
            expr init: (rat getExp) rand: (rad getExp).
        ].

        ^expr
    ]

    aoeWithNoNill [
        |change|

        expr ifVar: [
            change:= false.
        ]
        ifAbs: [
            change := false.
        ]
        ifApp: [
            |rator rand ratorExp randExp|

            rator := Lambda new: (expr rator).
            rand := Lambda new: (expr rand).

            change := rator aoeWithNoNill.
            change ifTrue: [
                expr init: (rator getExp) rand: (rand getExp).
                ^change.
            ].

            change := rand aoeWithNoNill.
            change ifTrue: [
                expr init: (rator getExp) rand: (rand getExp).
                ^change.
            ].

            ratorExp := rator getExp.
            randExp := rand getExp.

            ratorExp ifVar: [
                change := false.
            ]
            ifAbs: [
                |var body|
                var := ratorExp var.
                body := Lambda new: (ratorExp body).

                body substitute: var for: randExp. "If no steps, I would have to reduce the result as well."

                expr := (body getExp) dup.
                change := true.
            ]   
            ifApp: [
                change := false.
            ]

        ].

        ^change.
    ]
    aoe [
        expr ifVar: [
            expr := nil.
        ]
        ifAbs: [
            expr := nil.
        ]
        ifApp: [
            self aoeWithNoNill ifFalse: [
                expr := nil.
            ]
        ].

        ^expr.
    ]

    aoe: steps [
        | newExpr |
        newExpr := expr reduceWith: [:exp |
            ((Lambda new: exp) aoe)
        ] steps: steps.

        expr := newExpr.
        ^expr
    ]

    norWithNoNill [
        |change|

        expr ifVar: [
            change:= false.
        ]
        ifAbs: [
            |var body|

            var := (expr var).
            body := Lambda new: (expr body).

            change := body norWithNoNill.
            expr init: var body: (body getExp).
        ]
        ifApp: [
            |rator rand ratorExp randExp|

            rator := Lambda new: (expr rator).
            rand := Lambda new: (expr rand).

            ratorExp := rator getExp.
            randExp := rand getExp.

            ratorExp ifVar: [
                change := rand norWithNoNill.
                expr init: ratorExp rand: (rand getExp).
            ]
            ifAbs: [
                |var body|
                var := ratorExp var.
                body := Lambda new: (ratorExp body).
                body substitute: var for: randExp.

                expr := (body getExp) dup.
                change := true.
            ]   
            ifApp: [
                change := rator norWithNoNill.
                change ifTrue: [
                    expr init: (rator getExp) rand: (rand getExp).
                    ^change.
                ].

                change := rand norWithNoNill.

                expr init: (rator getExp) rand: (rand getExp).
            ]
        ].

        ^change.
    ]

    nor [
        expr ifVar: [
            expr := nil.
        ]
        ifAbs: [
            self norWithNoNill ifFalse: [
                expr := nil.
            ]
        ]
        ifApp: [
            self norWithNoNill ifFalse: [
                expr := nil.
            ]
        ].

        ^expr.
    ]

    nor: steps [
        | newExpr |
        newExpr := expr reduceWith: [:exp |
            ((Lambda new: exp) nor)
        ] steps: steps.

        expr := newExpr.
        ^expr
    ]
    
    etaWithNoNill [
        |change|

        expr ifVar: [
            change:= false.
        ]
        ifAbs: [
            |var body|

            var := (expr var).
            body := Lambda new: (expr body).

            change := body etaWithNoNill.
            change ifTrue: [expr init: var body: (body getExp).] 
            ifFalse: [
                (body getExp) ifVar: []
                ifAbs: []
                ifApp: [
                    |rator rand freeVarMap hadKey|

                    rator := (body getExp) rator.
                    rand := (body getExp) rand.

                    rand ifVar: [
                        ((rand name) = var) ifTrue: [
                            freeVarMap := rator freeVars: (Dictionary new).
                            hadKey := freeVarMap includesKey: var.

                            hadKey ifFalse: [
                                expr := rator.
                                change := true.
                            ]    
                        ]
                    ] ifAbs: [] ifApp: []
                ]
            ].
        ]
        ifApp: [
            |rator rand|

            rator := Lambda new: (expr rator).
            rand := Lambda new: (expr rand).

            change := rator etaWithNoNill.
            change ifTrue: [
                expr init: (rator getExp) rand: (rand getExp).
                ^change.
            ].

            change := rand etaWithNoNill.
            expr init: (rator getExp) rand: (rand getExp).
        ].

        ^change.
    ]

    eta [
        expr ifVar: [
            expr := nil.
        ]
        ifAbs: [
            self etaWithNoNill ifFalse: [
                expr := nil.
            ]
        ]
        ifApp: [
            self etaWithNoNill ifFalse: [
                expr := nil.
            ]
        ].

        ^expr.
    ] 

    eta: steps [
        | newExpr |
        newExpr := expr reduceWith: [:exp |
            ((Lambda new: exp) eta)
        ] steps: steps.

        expr := newExpr.
        ^expr
    ]
].
" lambdaParser := LambdaParser new: '(^x. ^y. (x y z x)) ((^z . z) x) (^y. y) r'. "
" ((Lambda new: (lambdaParser parse)) toDeBruijn) displayNl.  "


" ((Lambda new: (lambdaParser parse)) substitute: 'y' for: (LambdaAbs withVar: 'n' body: (LambdaVar withName: 'n'))) displayNl.  "

" ((Lambda new: (lambdaParser parse)) aoe:1) displayNl.  "
 