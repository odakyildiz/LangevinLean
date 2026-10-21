GRADIENT DESCENT - MATH AND LEAN
163 Anki review cards, from zero Lean knowledge to the complete proof.

IMPORT

Open Anki, choose File > Import, and select:
  GradientDescent_Math_and_Lean.apkg

The package includes all cards, their styled note type, and ten numbered
subdecks. No field mapping, add-on, or LaTeX installation is needed.
Equations use Anki's built-in MathJax. All cards start as new cards.

Official import guide: https://docs.ankiweb.net/importing/packaged-decks.html
Math rendering: https://docs.ankiweb.net/math.html

HOW TO REVIEW

Start with 01 Lean from zero, then 02 Proof roadmap. Continue through the
numbered proof stages in order. Reveal an answer only after trying to say
the mathematical fact or explain the Lean step in your own words.

Each card asks one main question. Its answer gives the matching mathematics,
plain-language tactic explanations, and a short memory cue. Code snippets
are copied exactly from the verified source; original line numbers are shown.
Expand "Find this step in the walkthrough" when you want the longer derivation.

The kinds are Math (recall a fact), Lean (decode syntax or a tactic), Bridge
(connect code and mathematics), and Checkpoint (reconstruct or check an argument).
Recall the meaning of a proof step rather than memorizing long code strings.

For the quick, repeated pass you described, use Anki's Browse window: select
the cards from one subdeck and use Preview to move through the questions
and answers. Use Anki's normal review mode for scheduled recall practice.

After a few passes, try to reconstruct these links without looking:
  1. Strong convexity -> the two gap bounds and strong gradient monotonicity.
  2. Auxiliary contraction -> stationary point -> unique global minimizer.
  3. Lipschitz gradient -> quadratic upper model -> one-step descent.
  4. Descent plus the gradient gap bound -> objective-gap contraction.
  5. Induction and squeezing -> both geometric bounds and both limits.

SUBDECKS

  01 Lean from zero          37 cards
  02 Proof roadmap          10 cards
  03 Strong convexity       21 cards
  04 Auxiliary contraction  11 cards
  05 Minimizer existence    10 cards
  06 Smoothness             22 cards
  07 One-step descent       14 cards
  08 Geometric decay        19 cards
  09 Full convergence        9 cards
  10 Endpoint checks        10 cards

The proof uses the actual step interval 0 < alpha < 2/L, derives minimizer
existence rather than assuming it, and uses the same clamped rate as the Lean
theorem. The auxiliary existence step is distinguished from the actual step.

FILES

  GradientDescent_Math_and_Lean.apkg  Complete ready-to-import deck.
  cards.tsv                         HTML field backup for editing; use the APKG
                                    for the complete styled subdeck import.
  cards_*.json                      Editable card text and exact source ranges.
  front.html / back.html            Anki note-type templates.
  card_style.css                    Desktop, mobile and night-mode styling.
  deck_manifest.json                Counts, card references and source hashes.
  Verification.txt                  Import, mathematics and layout checks.
  make_foundations.py               Regenerates beginner/roadmap author data.
  build_deck.py                     Builds and import-tests with Anki's backend.

REBUILD ON THIS MAC

  python3 GradientDescent/exposition/Flashcards/make_foundations.py
  PYTHONPATH=/Applications/Anki.app/Contents/Resources/app_packages \
    /opt/homebrew/bin/python3.13 \
    GradientDescent/exposition/Flashcards/build_deck.py

The builder uses isolated temporary collections. If the Lean source changes,
update the referenced ranges and explanations before rebuilding the cards.
