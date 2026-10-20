# Neon Stack

A falling-block game in a neon well. Fill a row and it clears.

[Play](neon-stack.html) · [How to play](how-to-play.html)

## Open it

Open `neon-stack.html` in a browser. Nothing to install and nothing to build.

The neon card with the same instructions is [`how-to-play.html`](how-to-play.html). Open that file in a browser too. GitHub shows this README as the front page.

## How a round works

Pieces fall in a 10 by 20 well. Slide them, turn them, and set them down. A full horizontal row clears, and the rows above it drop. The round ends when a new piece cannot enter. The game says "The stack reached the top."

The next three pieces are on screen. A ghost marks where a hard drop will land. Hold keeps the current piece and, if the hold was empty, brings out the next one. You can hold again after that piece locks.

The seven shapes (I, O, T, S, Z, J, L) come from a shuffled bag, so each shape appears once before the bag refills. If a turn is blocked, the piece slides a little to fit.

Every 10 lines raises the level. Pieces fall faster, and the music tempo rises with the level.

## Controls

| Keys | Action |
| --- | --- |
| Left, Right | Move. Hold the key to keep moving. |
| Down | Soft drop. Hold the key to keep dropping. |
| Space | Hard drop. The piece locks. |
| Up, X | Rotate clockwise. |
| Z, Ctrl | Rotate counterclockwise. |
| C | Hold. |
| P | Pause or resume. |
| R | Restart. |
| M | Mute or unmute. |
| Esc | Quit. Press R to play again. |

Pause, Restart, Random Song, and Mute are also buttons beside the well.

On a narrow screen, a pad under the well has move left, soft drop, move right, rotate counterclockwise, hard drop, and hold.

## Score

Line clears are multiplied by the level. At level 1:

| Lines | Name | Points |
| ---: | --- | ---: |
| 1 | Single | 100 |
| 2 | Double | 300 |
| 3 | Triple | 500 |
| 4 | Nova | 800 |

Clear again before you lock a piece that clears nothing, and a combo is added on top of the line score. The second clear in a row adds 50 times the level. The third adds 100 times the level. Each clear after that climbs by another 50 times the level.

Soft drop scores 1 point per cell. Hard drop scores 2 per cell. Drop points stay flat. They are not multiplied by the level.

## The boom

A line clear plays a whoosh, then a boom. Two booms when several lines clear. Mute turns off the music and the boom together.

## Music

Five tracks: Let’s Go!, Battle Loop, Borderline Space, Final Push, and Regular Battle. Random Song picks another one. Volume starts at 10%. Base tempo starts at 75% and climbs 5 points each level, up to 125%.

Music: "Neon Sign Circuit" by MintoDog. License: CC0.
