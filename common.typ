#import "@preview/curryst:0.6.0" as curryst: rule, prooftree
#import "@preview/theorion:0.4.1" as theorion: *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#import "@preview/cetz:0.4.2" as cetz: canvas

#import cosmos.fancy: *

#let drft = state("draft", none)

#let diagram(..args) = {
    context {
        let d = drft.get()
        if d == none or d.any(d => counter(heading).display(heading.numbering).starts-with(d)) {
            fletcher.diagram(..args)
        } else {
            rect(width: 5cm, height: 3cm)[the diagram commutes]
        }
    }
}
#let definition = cosmos.fancy.definition.with(breakable: true)
#let lemma = cosmos.fancy.lemma.with(breakable: true)
#let theorem = cosmos.fancy.theorem.with(breakable: true)
#let axiom = cosmos.fancy.theorem.with(breakable: true)
#let corollary = cosmos.fancy.corollary.with(breakable: true)
#let conjecture = cosmos.fancy.conjecture.with(breakable: true)

#let all(title, draft, bd) = {
    show: show-theorem
    show raw.where(lang: "derivation") : it => {
        let kwc = rgb("#F0DFAF")
        let idc = rgb("#DFAF8F")
        let typc = rgb("#93E0E3")
        set text(fill: white)
        show: block.with(fill: rgb("#383838"), inset: 8pt, radius: 5pt)
        show regex("\b[a-z]\w*\b") : text.with(fill: idc)
        show regex("\b[A-Z]\w*\b") : text.with(fill: typc)
        show regex("\b(let[*]?|Let[*]?|in|fun|λ|Λ|π₁|π₂)\b") : text.with(weight: "bold", fill: kwc)
        show regex("--.*") : line => emph(text(line, fill: gray))
        show regex(":=|:|=>|⊢") : text.with(weight: "bold")
        show regex("\$(.*?)\$") : re => eval(re.text, mode: "markup")
        it
    }
    set text(font: "New Computer Modern", size: 11pt)
    set par(justify: true)
    set document(title: title, author: "Adrien Mathieu")
    drft.update(draft)
    v(1fr)
    align(center, text(25pt)[*#title;*])
    align(center, text(15pt, [Adrien #smallcaps[Mathieu]]))
    v(2fr)
    outline(
        target: heading.where(supplement: [Section]),
        depth: 2,
    )
    v(2fr)
    pagebreak()

    set page(
        numbering: "1",
        footer: context if page.numbering != none {
            align(center)[-- #counter(page).display(page.numbering) --]
        },
        header: context {
            set text(size: 10pt)
            let secs = query(heading.where(level: 1).after(here()))
            let sec = if secs.len() != 0 and secs.first().location().page() == here().page() {
                secs.first()
            } else {
                query(heading.where(level: 1).before(here())).last()
            }
            if sec.numbering != none {
                [*#sec.supplement #numbering(sec.numbering, counter(heading).at(sec.location()).at(0));*]
            }
            h(1fr)
            [_#sec.body;_]
        },
    )
    set heading(numbering: "1.")
    counter(page).update(1)

    bd
}
