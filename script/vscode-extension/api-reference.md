# Script API Reference

Built-in functions of the Way of the Samurai script language. See `.claude/skills/samurai-script/syntax.md` for language syntax and `.claude/skills/samurai-script/SKILL.md` for constant prefix meanings (CHID, MTAS, SAY, etc.). The `bool` type denotes an integer constrained to `#ON` / `#OFF`.

### SetCharAdd

- **Obfuscated name:** C00
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to add
  - `life` (int) — initial HP
  - `x` (float) — world X coordinate
  - `y` (float) — world Y coordinate (height)
  - `z` (float) — world Z coordinate
  - `angle` (float, optional) — facing angle
- **Returns:** none
- **Description:** Loads a character and adds them to the game. The `life` parameter sets both the current and maximum HP.

### SetCharDel

- **Obfuscated name:** C01
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to delete
- **Returns:** none
- **Description:** Removes a character from the game and deallocates its resources. Typically called within the `NpcOut` handler after hiding the character with `SetCharDraw`. Active usages appear in `MapOut` definitions (p01/e03, p01/e20), where the Japanese comment 削除 ("delete") confirms intent.

### SetCharDraw

- **Obfuscated name:** C02
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to show or hide
  - `visible` (bool) — `#ON` to show, `#OFF` to hide
- **Returns:** none
- **Description:** Toggles character visibility on the current map. Hiding a character (`#OFF`) is typically followed by cleanup such as `SetCharDel` or AI removal; showing (`#ON`) restores the character. Used during map transitions and NPC spawn/despawn flows. For bulk operations see `SetCharDrawOnList` / `SetCharDrawOffList`.

### SetCharLife

- **Obfuscated name:** C03
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to modify; the special value `#ONESELF` refers to the script's owning character
  - `life` (int) — current HP value to set; `-1` is used in some death/cleanup contexts
- **Returns:** none
- **Description:** Sets a character's current life (HP). Used to initialize NPC HP (e.g. `$SetCharLife #CHID_HYUGA, 1110`), to restore full health by passing `GetCharLifeMax`, or to put a character into a weakened state. Often paired with `SetCharLifeMax` at event init and with `SetCharDead` when reviving a downed character.

### SetCharLifeMax

- **Obfuscated name:** C04
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to modify
  - `maxLife` (int) — maximum HP value to set
- **Returns:** none
- **Description:** Sets a character's maximum HP. Almost always called alongside `SetCharLife` during event setup to size NPC and enemy health pools. Observed values range from a few hundred (low-tier enemies) up to 9999 (bosses).

### SetCharPos

- **Obfuscated name:** C05
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to position
  - `x` (float) — world X coordinate
  - `y` (float) — world Y coordinate (height)
  - `z` (float) — world Z coordinate
  - `unknown` (any, optional) — unknown, typically `#NULL`; rarely used. value is irrelevant; behavior is triggered simply by the presence of the argument.
- **Returns:** none
- **Description:** Teleports a character to the given 3D coordinates. Commonly used at map entry points to place `CHID_SHUJINKO` and during cutscene setup to position NPCs. Often paired with `SetCharDir2` to set facing direction in the same step. Most call sites use only three positional arguments.

### SetCharDir

- **Obfuscated name:** C06
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to orient
  - `target` (CHID, or float x, float y, float z) — either a character ID to face, or three floats for a 3D facing vector
- **Returns:** none
- **Description:** Sets a character's facing. Two forms: passing a character ID rotates the character to face that character (e.g. `$SetCharDir #ONESELF, #CHID_SHUJINKO`); passing three floats orients toward that world point (e.g. `$SetCharDir #ONESELF, 3.32, 4.87, 44.77`). Compare with `SetCharDir2`, which always takes XYZ. Some surrounding Japanese comments mark these calls as 暫定 ("provisional"), suggesting the system was iterated on.

### SetCharMove

- **Obfuscated name:** C07
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to move; `#ONESELF` refers to the script's owning character
  - `motion` (COMMAND) — movement command (e.g. `#COMMAND_WALK`, `#COMMAND_RUN`, `#COMMAND_BACK`)
  - `x` (float) — destination X
  - `y` (float) — destination Y
  - `z` (float) — destination Z
- **Returns:** (int) — task ID for the async movement; can be passed to `DelTaskID` to cancel
- **Description:** Walks/runs a character to a 3D destination using the chosen motion. Returns a task ID; scripts commonly store it and later cancel via `DelTaskID` to interrupt movement mid-path. Typical call: `$SetCharMove #CHID_SHUJINKO, #COMMAND_WALK, 1.92, 0.43, -14.43`.

### SetCharAction

- **Obfuscated name:** C08
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to act
  - `command` (COMMAND) — action verb (e.g. `#COMMAND_MOTION`, `#COMMAND_WEAPON_ON`, `#COMMAND_WEAPON_OFF`, `#COMMAND_CANCEL`, `#COMMAND_OPEN`)
  - `param` (varies) — parameter for the command (e.g. an `MTAS_*` for `#COMMAND_MOTION`, `#PARAM_WEAPON_F` for weapon commands, `0` otherwise)
  - `_unused` (int) — appears to be unused; always `0` in observed calls
- **Returns:** (int) — task ID for the action, capturable via `|` for completion tracking
- **Description:** Generic action dispatcher for characters. Used to play one-off animations (`MTAS_TUMBLE_A`, `MTAS_DANGER_A`), draw/sheathe weapons, cancel current actions, and trigger opens. Common pattern: `#TaskID | $SetCharAction #CharID, #COMMAND_MOTION, #MTAS_...`.

### StartCharTrace

- **Obfuscated name:** C09
- **Availability:** all versions
- **Arguments:**
  - `follower` (CHID) — character that will pursue
  - `target` (CHID) — character to follow (often `CHID_SHUJINKO`)
  - `motion` (COMMAND) — movement command used while following (e.g. `#COMMAND_WALK`, `#COMMAND_RUN`)
- **Returns:** (object) — trace handle to be passed to `StopCharTrace`
- **Description:** Starts a continuous follow behavior — `follower` chases `target` using `motion`. The returned handle should be stored and later passed to `StopCharTrace` to end the pursuit. Used widely in scripted sequences where NPCs accompany the player.

### StopCharTrace

- **Obfuscated name:** C0A
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character whose trace should end
  - `traceHandle` (object) — handle previously returned by `StartCharTrace`
- **Returns:** none
- **Description:** Ends a follow behavior previously initiated by `StartCharTrace`. The handle argument must be the exact object returned by that call.

### GetCharStatus

- **Obfuscated name:** C0B
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to query
  - `eventId` (EVENT) — character event to check (e.g. `#EVENT_WEAPON_ON`)
- **Returns:** (bool) — `#ON` if the event is currently active for the character, otherwise `#OFF`
- **Description:** Queries whether a particular character-event state is active. Most commonly used with `#EVENT_WEAPON_ON` to detect whether a character has drawn their weapon. Related: `SetEventMode`, `AddEventMode`, `SubEventMode` modify character event state.

### SetCharTarget

- **Obfuscated name:** C0C
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character whose target is being set
  - `target` (CHID, optional) — target character; if omitted, clears the target
  - `_extra` (object, optional) — observed only as `#NULL`; purpose unclear
- **Returns:** none
- **Description:** Sets a character's combat target. With no target argument, clears it. With a target (and trailing `#NULL`), assigns it — used in battle scripts to direct AI at the player or another character. Pair with `GetCharTargetID` to read the current target.

### SetCharDir2

- **Obfuscated name:** C0D
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to orient; `#ONESELF` allowed
  - `x` (float) — X of the world point to face
  - `y` (float) — Y of the world point to face
  - `z` (float) — Z of the world point to face
- **Returns:** none
- **Description:** Orients a character toward a specific XYZ point. Unlike `SetCharDir` (which can take a character ID), `SetCharDir2` only accepts coordinates. Frequently called immediately after `SetCharPos` during cutscene/map-entry setup.

### GetCharPos

- **Obfuscated name:** C0E
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to query
  - `axis` (int) — which coordinate: `0` = X, `1` = Y, `2` = Z
- **Returns:** (float) — the requested coordinate
- **Description:** Reads a single component of a character's world position. Inverse of `SetCharPos` (which writes all three at once). Used for distance math, conditional spawn positioning, and so on. Typical: `#xx | $GetCharPos #id, 0`.

### GetCharRange

- **Obfuscated name:** C0F
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — first character
  - `other` (CHID, or float x, float y, float z) — second character, or a world point
  - `distance` (float) — distance threshold in game units
- **Returns:** (bool) — `#ON` if within `distance`, else `#OFF`
- **Description:** Proximity check. Returns whether two characters (or a character and a world point) are within `distance`. Used extensively in walker logic and event triggers: `?i (($GetCharRange #CHID_SHUJINKO, #a, 5.0) eq #ON) {...}`.

### GetCharLife

- **Obfuscated name:** C10
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to query; `#ONESELF` allowed
- **Returns:** (int) — current HP
- **Description:** Reads a character's current HP. Drives gameplay branches like `?i (#player_life le 400) {...}`. Companions: `SetCharLife` (write), `GetCharLifeMax` (max), `GetCharLifeRatio` (percent).

### GetCharLifeMax

- **Obfuscated name:** C11
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to query
- **Returns:** (int) — the character's maximum HP
- **Description:** Reads a character's max HP. Used to scale enemy HP relative to the player (e.g. dividing the player's max by 3 to seed an NPC) and as the argument to `SetCharLife` to restore full health.

### SetCharForm

- **Obfuscated name:** C12
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to configure
  - `visible` (bool) — `#ON` to show, `#OFF` to hide
  - `idleMotion` (MTAS, optional) — idle animation to enter (e.g. `#MTAS_STOP`, `#MTAS_DANGER_A`, `#MTAS_SUWA_B`)
- **Returns:** none
- **Description:** Spawns/poses a character: combined visibility toggle and initial idle animation. Used during `Init`/`Start` setup to place characters in scene-appropriate poses. Compare with `SetCharDraw`, which only toggles visibility.

### SetCharMotion

- **Obfuscated name:** C13
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to animate; `#ONESELF` allowed
  - `motion` (MTAS) — animation to play (e.g. `#MTAS_STOP`, `#MTAS_TALK_F`)
  - `loop` (bool) — `#ON` to loop, `#OFF` to play once
- **Returns:** (int) — task ID, usable with `DelTaskID`, `SetWaitEndTask`, etc.
- **Description:** Plays a motion on a character. The returned task ID lets scripts wait on completion or cancel mid-play. Typical: `#MotTaskID | $SetCharMotion #CharID, #MTAS_STOP, #OFF`.

### SetCharNoDamageMode

- **Obfuscated name:** C14
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to modify
  - `enabled` (bool) — `#ON` to make invulnerable, `#OFF` to restore normal damage
- **Returns:** none
- **Description:** Toggles damage invulnerability on a character. Used to protect NPCs during cinematics, scripted moments, and tutorials. Usually re-disabled (`#OFF`) once the protected sequence ends. Compare with `SetCharNoCollMode`, which toggles collision rather than damage.

### GetCharDead

- **Obfuscated name:** C15
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to query
- **Returns:** (bool) — `#ON` if the character is dead, `#OFF` if alive
- **Description:** Reports whether a character has been killed. Used to gate dialogue, skip post-mortem actions, and prevent interaction with corpses. Related: `SetCharDead` (write the dead flag), the `Dead` callback (fires on any death), and the `SayDead` callback (fires when a character with the "say dead" flag dies).

### SetCharHoldObj

- **Obfuscated name:** C16
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character that will carry the object
  - `objId` (OBJ) — world object to attach (e.g. `#OBJ_ISU_A` chair, `#OBJ_KINKO` safe, `#OBJ_UBAGURUMA_SET` baby carriage)
- **Returns:** none
- **Description:** Attaches a world object to a character so they visibly hold/carry it. Inverse: `SetCharRelObj` releases the held object.

### SetCharRelObj

- **Obfuscated name:** C17
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character currently holding an object
- **Returns:** none
- **Description:** Releases whatever world object the character is currently holding. Scripts commonly guard the call with a `GetObjChar` check (proceed only if the character holds an object). Inverse of `SetCharHoldObj` ("Rel" = release).

### SetCharNeckAction

- **Obfuscated name:** C18
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — target character
  - `duration` (float) — animation duration in seconds
  - `yaw` (int) — horizontal angle in degrees (0 = forward, +right, −left)
  - `pitch` (int) — vertical angle in degrees (+up, −down)
- **Returns:** (int) — task ID, cancellable via `DelTaskID`
- **Description:** Animates the character's head/neck to aim in a direction — used to make characters glance at or track another character (commonly the player) during dialogue. Japanese comments such as 首の向き：主人公方向へ ("neck direction: toward the player") confirm the intent.

### SetCharStop

- **Obfuscated name:** C19
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to freeze
  - `enabled` (bool) — `#ON` to freeze, `#OFF` to resume
- **Returns:** none
- **Description:** Freezes/unfreezes a character's movement and animations. Used during cutscenes to hold NPCs still while dialogue plays; often paired with `SetPadMode` when ceding or reclaiming player input. Boss sequences toggle several characters in rapid succession.

### GetCharLifeRatio

- **Obfuscated name:** C1A
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to query
- **Returns:** (int) — life as a percentage (0–100) of max HP
- **Description:** Returns the character's current HP as a percentage of max — convenient for thresholded health checks (e.g. "below 50%"). Equivalent to dividing `GetCharLife` by `GetCharLifeMax` and scaling.

### SetCharFriendFlag

- **Obfuscated name:** C1B
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character whose relationship flag is being set
  - `status` (FRIEND) — relationship value, e.g. `#FRIEND_NOMEET` (0), `#FRIEND_MEET` (1), `#FRIEND_FELLOW` (2, ally), `#FRIEND_ENEMY` (3)
- **Returns:** none
- **Description:** Sets the player↔character relationship flag — tracks whether the player has met the character and whether they are now an ally or enemy. Affects subsequent dialogue and behavior. Read via `GetCharFriendFlag`. Note this is a per-character "have-we-met / are-we-friends" flag, distinct from faction-level `FOOTING_*` relationships.

### GetCharFriendFlag

- **Obfuscated name:** C1C
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to query; `#ONESELF` allowed
- **Returns:** (FRIEND) — current relationship flag (`#FRIEND_NOMEET`, `#FRIEND_MEET`, `#FRIEND_FELLOW`, `#FRIEND_ENEMY`)
- **Description:** Reads the relationship flag for a character. Used to gate dialogue options and conditional behavior based on whether the player has met them or established alliance/enmity. Companion to `SetCharFriendFlag`.

### GetCharThrowCount

- **Obfuscated name:** C1D
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to query
- **Returns:** (int) — number of throws/grapples performed
- **Description:** Returns how many throw (grapple) moves the character has performed. Used in p01/e01 (Dona scene) where reaching a threshold (e.g. `?i (#ThrowCount ge 5)`) triggers samurai-value adjustments or event branches. Japanese comment 投げた回数 ("times thrown") confirms intent.

### SetCharGroupID

- **Obfuscated name:** C1E
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to assign
  - `groupId` (FOOTING) — faction/group, e.g. `#FOOTING_KURONAMA`, `#FOOTING_AKADAMA`, `#FOOTING_SEIHU`, `#FOOTING_SHUKUBA`, `#FOOTING_NORMAL`, `#FOOTING_EVENT`, `#FOOTING_PLAYER`
- **Returns:** none
- **Description:** Assigns a character to a faction "footing", which drives ally/enemy AI behavior and damage-targeting rules. `#FOOTING_EVENT` is used for temporary cutscene groupings; `#FOOTING_NORMAL` for generic neutrals. Faction-vs-faction relationships are set elsewhere via `SetFootingFlag`-family functions.

### GetCharTargetID

- **Obfuscated name:** C1F
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character whose target is queried
- **Returns:** (CHID) — current target's character ID, or a null/empty value if none
- **Description:** Reads which character is currently being targeted in combat. Used to branch on targeting state, e.g. `?i (#target eq #CHID_YAKUNIN_6) {...}`. Companion to `SetCharTarget`.

### SetCharDrawOnList

- **Obfuscated name:** C20
- **Availability:** all versions
- **Arguments:**
  - `charIds...` (CHID, variadic) — one or more character IDs to make visible
- **Returns:** none
- **Description:** Bulk version of `SetCharDraw #ON` — shows multiple characters in a single call. Typical use during event setup to spawn an ensemble at once: `$SetCharDrawOnList #CHID_SHUJINKO, #CHID_TESHIN, #CHID_SHIRETOKO, #CHID_KUROZAKO3_0`. Inverse: `SetCharDrawOffList`.

### SetCharDrawOffList

- **Obfuscated name:** C21
- **Availability:** all versions
- **Arguments:**
  - `charIds...` (CHID, variadic) — one or more character IDs to hide
- **Returns:** none
- **Description:** Bulk version of `SetCharDraw #OFF` — hides multiple characters at once. Common during map exits and scene transitions. Inverse: `SetCharDrawOnList`.

### SetCharNoCollMode

- **Obfuscated name:** C22
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to modify
  - `enabled` (bool) — `#ON` to disable collision, `#OFF` to restore it
- **Returns:** none
- **Description:** Toggles a character's no-collision mode, allowing them to be rendered and moved without physical interaction with other characters/geometry. Useful during cutscenes or when overlapping characters must briefly occupy the same space. Compare with `SetCharNoDamageMode`, which controls damage rather than collision.

### SetCharShowList

- **Obfuscated name:** C23
- **Availability:** all versions
- **Arguments:**
  - `mode` (bool) — `#ON` to restrict visibility to the listed characters, `#OFF` to show everyone
  - `charIds...` (CHID, variadic) — character IDs to keep visible when `mode` is `#ON`; ignored when `#OFF`
- **Returns:** none
- **Description:** Whitelist-style visibility control. With `#ON`, only the listed characters remain visible (all others hidden); with `#OFF`, everyone is shown again. Different from `SetCharDrawOnList`/`SetCharDrawOffList`, which simply show/hide the listed characters without affecting non-listed ones.

### SetCharDead

- **Obfuscated name:** C24
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to affect; `#ONESELF` supported
  - `dead` (bool) — `#ON` to mark dead, `#OFF` to revive
- **Returns:** none
- **Description:** Writes the dead flag on a character. Used to enforce a story death or to revive after a staged death. Counterpart to `GetCharDead`. The `Dead` callback fires on any death; `SayDead` fires for characters whose "say dead" flag is set.

### SetCharTalkOver

- **Obfuscated name:** C25
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to affect
- **Returns:** none
- **Description:** Has no effect; implementation is incomplete. Presumably would have ended dialogue for the given character.

### SetCharLevel

- **Obfuscated name:** C26
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to configure
  - `level` (int) — difficulty/skill tier (0–3 observed)
- **Returns:** none
- **Description:** Sets a character's AI skill/difficulty level. Higher values yield tougher combat behavior. Typically applied to enemy NPCs and zako during event setup.

### SetCharPosAdjust

- **Obfuscated name:** C27
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to adjust
- **Returns:** none
- **Description:** Snaps a character's position to a valid spot (typically on the ground / out of geometry), called immediately after `SetCharPos` during cutscene/map-entry setup. Acts as a collision-aware fix-up after a raw teleport.

### SetCharFace

- **Obfuscated name:** C28
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to animate
  - `expression` (MTAS) — facial/expression animation (e.g. `#MTAS_SU_A` neutral lip-sync, `#MTAS_IKA_B` angry, `#MTAS_KANA_B` sad)
  - `duration` (float) — duration in seconds
- **Returns:** (int) — task ID, cancellable via `DelTaskID`
- **Description:** Drives a character's face/lip-sync animation while speaking. The `MTAS_*` constants encode both emotion and mouth shape. Task ID lets scripts cancel mid-expression. Typically used in combination with `SetCharHiFaceMode` and `Say`.

### SetCharWakiZako

- **Obfuscated name:** C29
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to designate
  - `enabled` (bool) — `#ON` to designate as a side/escort zako, `#OFF` to clear
- **Returns:** none
- **Description:** Marks a character as a 脇雑魚 ("waki zako") — a respawning sidekick/escort underling. Toggled off when the attendant is killed and/or when a threshold number of enemies have been defeated.

### SetCharDirFollow

- **Obfuscated name:** C2A
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character whose facing will track
  - `target` (CHID) — character to continuously face
- **Returns:** (int) — task ID; can be stored and cancelled via `DelTaskID`
- **Description:** Starts continuous "look-at" tracking — `charId` rotates over time to keep facing `target`. Used during dialogue/cutscenes to keep characters oriented at each other as they move. Japanese comment 向き追従 ("facing follow") confirms intent.

### SetCharDaikonFlag

- **Obfuscated name:** C2B
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to modify
  - `value` (int) — new daikon flag value
- **Returns:** none
- **Description:** Sets a character's daikon flag (see `GetCharDaikonFlag`) to the given value.

### GetCharDaikonFlag

- **Obfuscated name:** C2C
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to query
- **Returns:** (int) — current daikon flag value
- **Description:** Reads a character's "daikon flag" (大根フラグ — literally "radish flag"). Modified by `AddCharDaikonFlag` and `SubCharDaikonFlag`. In code terms, a character's daikon flag controls how many times the `GiveMeDaikon` function can be used to make them drop a healing item. In gameplay terms, scripts treat this as a measure of how much the character likes the player. Performing actions that the character likes will increase their daikon flag, while performing actions they dislike will decrease their daikon flag. In the game's final battles, while fighting alongside this character, the player may "cash in" the daikon they've earned with the character by asking them for healing items a number of times equal to their daikon flag.

### SubCharDaikonFlag

- **Obfuscated name:** C2D
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to modify
  - `amount` (int) — value to subtract from the flag
- **Returns:** none
- **Description:** Decrements the character's daikon flag by `amount`. Inverse of `AddCharDaikonFlag`; read via `GetCharDaikonFlag`.

### AddCharDaikonFlag

- **Obfuscated name:** C2E
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to modify
  - `amount` (int) — value to add to the flag
- **Returns:** none
- **Description:** Increments the character's daikon flag by `amount`. Used to reward character behavior at key beats (e.g. +1 to Shiretoko / +2 to Teshin after p02/e15; +1 to Doujima after defeating Hyuga in p04/e19). Inverse of `SubCharDaikonFlag`; read via `GetCharDaikonFlag`.

### SetCharDeathBlow

- **Obfuscated name:** C2F
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to mark
- **Returns:** none
- **Description:** Triggers a character to attack with a special finishing move. Depending on the situation, this may not always be a one-hit kill.

### SetCharWaiting

- **Obfuscated name:** C30
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to put into waiting stance
- **Returns:** none
- **Description:** Puts a character into a combat "waiting" stance — a ready-to-fight idle used during duel pacing (typically right after a 待った "wait" dialogue prompt). Unlike `SetCharStop`, which fully freezes a character, `SetCharWaiting` lets them play a standing-ready animation.

### SetCharDropWeapon

- **Obfuscated name:** C31
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character who drops their weapon
- **Returns:** none
- **Description:** Forces a character to drop their equipped weapon to the ground. Used in scripted defeat or disarm beats (e.g. p05/e25 — 茂吉さん、武器落とす "Mokichi drops his weapon" — after a `MTAS_DEAD02` death animation).

### SetCharTechFlashMode

- **Obfuscated name:** C32
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to affect
  - `enabled` (bool) — `#ON` to enable, `#OFF` to disable
- **Returns:** none
- **Description:** Toggles a character's 閃く ("flash of insight") effect — the visual cue for the moment a special technique is learned or executed. Seen in p00/e02 with the comment ◆閃く主人公◆ ("◆protagonist flashes◆") around the moment the player learns a move.

### SetCharExplosion

- **Obfuscated name:** C33
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character at whose position the explosion occurs
- **Returns:** none
- **Description:** Triggers an explosion VFX centered on a character. Appears in dramatic combat moments (e.g. p04/e12, p04/e19). Likely also applies blast knockback/damage to nearby characters, though the exact gameplay effect is not fully confirmed from script context.

### SetCharPosFixMode

- **Obfuscated name:** C34
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to pin
  - `enabled` (bool) — `#ON` to pin in place, `#OFF` to release
- **Returns:** none
- **Description:** Pins a character at their current position so AI movement cannot displace them. Used during cutscenes/dialogue to keep an NPC anchored while still allowing animations. Compare with `SetCharStop` (full freeze) and `SetCharNoCollMode` (collision off).

### SetCharHiFaceMode

- **Obfuscated name:** C35
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to affect; `#ONESELF` supported
  - `enabled` (bool) — `#ON` to enable, `#OFF` to disable
- **Returns:** none
- **Description:** Toggles high-fidelity face animation mode, enabling detailed `SetCharFace` expressions during dialogue/cutscenes. Usually disabled again once the scripted facial sequence ends. Surrounding Japanese comments often reference FACEアニメ ("face anime[ation]").

### SetCharWeapon

- **Obfuscated name:** C36
- **Availability:** us_proto, us, kanzenban, psp (added in the North American release)
- **Arguments:**
  - `charId` (CHID) — character to equip
  - `weaponId` (int) — numeric weapon ID
- **Returns:** none
- **Description:** Equips a character with a specific weapon. Used during event setup to assign weapons to NPCs (e.g. p05/e20 fixes two government officers' katana, IDs 35 and 21; p05/e25/e26 give Yakunin-6 IDs 24 and 40). Weapon IDs are raw integers — no `WPN_*` constants observed.

### SetBattleCamera

- **Obfuscated name:** C37
- **Availability:** all versions
- **Arguments:**
  - `enabled` (bool) — `#ON` to engage the battle camera, `#OFF` to release it
- **Returns:** none
- **Description:** Switches the camera into/out of battle-mode framing. Typically called `#ON` after setting up AI and targets (e.g. `SetAIChar`, `SetCharTarget`) at the start of a fight, and `#OFF` when dialogue or cutscene-style framing should resume.

### SetCameraPos

- **Obfuscated name:** C38
- **Availability:** all versions
- **Arguments:**
  - `mode` (CAMERA) — camera mode (e.g. `#INIT` to reset, `#CAMERA_WORLD` for an absolute world-space placement)
  - `camX, camY, camZ` (float, optional) — camera position
  - `lookX, lookY, lookZ` (float, optional) — look-at target
  - `upX, upY, upZ` (float, optional) — up vector (typically `0, 1, 0`)
  - `interpolate` (bool, optional) — `#ON` to smoothly transition
  - `duration` (int, optional) — transition duration
- **Returns:** none
- **Description:** Positions the camera in world space. The short form (`#INIT`, optionally with a bool) resets to default behavior; the full form with `#CAMERA_WORLD` provides full cinematic control over position, look-at, up vector, and interpolation.

### SetBustupCamera

- **Obfuscated name:** C39
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to frame
  - `_a` (int) — observed as `0`; purpose unknown
  - `left, top, right, bottom` (float) — viewport region of the framing (normalized 0..1)
  - `_b` (int) — observed as `0`; purpose unknown
- **Returns:** none
- **Description:** Sets up a "bustup" (chest-up) close-up camera framing for a character — an anime-style portrait shot used in dialogue beats. Viewport rectangle controls the framing region. Used widely in story scenes.

### SetSoloCamera

- **Obfuscated name:** C3A
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to frame
  - `x, y, z` (float) — camera offset relative to the character
  - `pitch` (float) — vertical camera angle
  - `distance` (float) — distance from the character
  - `roll` (float) — camera roll
- **Returns:** none
- **Description:** Frames a single character with a custom orbit position. Used heavily for dramatic single-character beats (e.g. 抜刀カメラ "draw-sword camera"). Almost always paired with `SetCameraMoveSpeed` (called first to set transition pace) and `SetFixCamera` (to lock the resulting shot).

### SetFixCamera

- **Obfuscated name:** C3B
- **Availability:** all versions
- **Arguments:**
  - `target` (CHID, or `#INIT`, or `-1`) — character to lock the camera onto; `#INIT` / `-1` releases the fixed camera
  - `_a` (int, optional) — observed as `0`
  - `_b` (int, optional) — rarely supplied; purpose unclear
- **Returns:** none
- **Description:** Locks the camera onto a character (or world position) for cinematic stability. Usually called right after `SetSoloCamera` to "stamp" the current shot. Pass `-1` / `#INIT` to release.

### SetTwoShotCamera

- **Obfuscated name:** C3C
- **Availability:** all versions
- **Arguments:**
  - `char1` (CHID) — first character in the frame
  - `char2` (CHID) — second character in the frame
  - `zoom` (float) — distance/zoom factor (≈1.0 typical)
  - `duration` (float) — transition time
- **Returns:** none
- **Description:** Cinematic "two-shot" framing — positions the camera to frame two characters together for dialogue/confrontation beats. Commonly used alongside `SetCutCamera` and `SetFixCamera`.

### SetVsCamera

- **Obfuscated name:** C3D
- **Availability:** all versions
- **Arguments:**
  - `player1` (CHID, or `#INIT`, or `-1`) — first character in versus match
  - `player2` (CHID, or `#INIT`, or `-1`) — second character in versus mode
- **Returns:** none
- **Description:** Versus-mode camera setup. Only called from engine-bound hard-coded scripts with both arguments set to `-1`. Likely the framing used in the dueling/versus modes.

### SetRotateCamera

- **Obfuscated name:** C3E
- **Availability:** all versions
- **Arguments:**
  - `rotationSpeed` (float) — angular speed (positive/negative for direction; typical values ±0.0003 to ±0.005)
- **Returns:** none
- **Description:** Starts a continuous orbital rotation around the current camera focus. Used during cutscenes (in conjunction with `SetSoloCamera`/`SetFixCamera`) to create a slow circling/dolly effect. Rotation persists until overridden (e.g. by another camera-setup call).

### SetCutCamera

- **Obfuscated name:** C3F
- **Availability:** all versions
- **Arguments:**
  - `cameraMode` (CAMERA) — e.g. `#CAMERA_INIT` (-1), `#CAMERA_WORLD` (0), `#CAMERA_CHAR` (1), `#CAMERA_2CHAR` (2), `#CAMERA_CHAR2` (3)
- **Returns:** none
- **Description:** Performs a hard cut to a new camera mode. Used to switch between world-space, single-character, and two-character framing during cutscenes; typically followed by `SetSoloCamera`/`SetTwoShotCamera` to fill in the specifics.

### SetCameraMoveSpeed

- **Obfuscated name:** C40
- **Availability:** all versions
- **Arguments:**
  - `speed` (float) — movement-speed multiplier for subsequent camera transitions
- **Returns:** none
- **Description:** Sets how quickly the camera interpolates during the next camera setup. Typical cutscene values are 3.0–4.0; extreme values like 0.005 (very slow) or 15.0 (snap) appear for special beats. Persistent — almost always called immediately before `SetSoloCamera`.

### SetEventMode

- **Obfuscated name:** C42
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to configure; `#ONESELF` allowed
  - `eventModes...` (EVENT, variadic) — `EVENT_*` constants and/or `#INIT`/`#ON`/`#OFF` control flags
- **Returns:** none
- **Description:** Replaces the character's active set of event modes wholesale. Each `EVENT_*` listed enables the corresponding callback (`Damage`, `TimeOut`, `WeaponOn`, etc.). For incremental changes use `AddEventMode` (enable) and `SubEventMode` (disable); read state with `GetCharStatus`. These functions control whether the character _receives_ the given events, not whether they trigger them for other characters.

### AddEventMode

- **Obfuscated name:** C43
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to modify; `#ONESELF` allowed
  - `eventModes...` (EVENT, variadic) — modes to enable (e.g. `#EVENT_BORDERLINE`, `#EVENT_LINEVIEW`, `#EVENT_MAPOUT`, `#EVENT_DAMAGE`, `#EVENT_WEAPON_ON`, `#EVENT_TALK`, `#EVENT_TIMEOUT`)
- **Returns:** none
- **Description:** Additive form of `SetEventMode` — enables the listed event modes without clearing existing ones. Used to re-enable handlers after a timeout or other transition. Inverse: `SubEventMode`.

### SubEventMode

- **Obfuscated name:** C44
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to modify
  - `eventModes...` (EVENT, variadic) — modes to disable
- **Returns:** none
- **Description:** Removes the listed event modes from a character's active set, leaving the rest intact. Inverse of `AddEventMode`; the full-replace form is `SetEventMode`.

### SetLineAction

- **Obfuscated name:** C45
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to configure
  - `limit0` (float) — radius of the first bounding box
  - `limit1` (float) — radius of the second bounding box
  - `limit2` (float) — radius of the second bounding box
  - `limit3` (float) — radius of the fourth bounding box
- **Returns:** none
- **Description:** Defines invisible trigger volumes anchored to a character. The trigger volumes are cubes, not spheres (hence the "line" name). When another character enters or exits one of the volumes, the engine fires `Join` / `Leave` events (requires event mode `EVENT_BORDERLINE` to be enabled for the receiver). The third argument to `Join` / `Leave` is the index of the bounding volume that was triggered. Compare with `SetPosLineAction` (anchored to a world position instead) and `SetLineViewAction` (sight-cone variant).

### SetCharWatch

- **Obfuscated name:** C46
- **Availability:** all versions
- **Arguments:**
  - `watcher` (CHID) — the character who is watching the other character
  - `target` (CHID, or `#INIT`, or `-1`) — the target character being watched, or `-1`/`#INIT` to disable the watch
  - `watchType` (WATCH, optional) — what to watch for. Ignored if `target` is `-1`/`#INIT`. Remaining arguments depend on the `watchType`:
    - `WATCH_LEAVE`
      - `limit` (float) — radius of the bounding box to watch
    - `WATCH_STOP`
      - No additional arguments
    - `WATCH_OBJECT`
      - `drop` (bool) — `#ON` to watch for object drop, `#OFF` to watch for object pick up
      - `object` (OBJ) — an object ID (e.g. `#OBJ_KINKO`)
- **Returns:** none
- **Description:** Configures triggers that fire the `Watch` callback when a character meets a condition (most commonly: picks up or drops a specific object). On fire, the `Watch` callback receives the monitored character plus a `param`. The watch is cleared upon being triggered. Event mode `EVENT_WATCH` must be enabled for `watcher`. Exact behavior depends on `watchType`:
  - `WATCH_LEAVE` — creates a bounding cube of radius `limit` centered on `target`'s position at the time the watch is set. Event fires when `target` leaves the bounding volume. `param` is a boolean indicating whether `target` exited the bounding volume in the direction of `watcher`.
  - `WATCH_STOP` — fires when `target`'s animation is `MTAS_STOP`, `MTAS_E_STOP`, or `MTAS_I_STOP`. `param` is always `0`.
  - `WATCH_OBJECT` — fires when `target` is holding a particular object or not holding an object. This is not actually triggered by the action of picking up or dropping an object, but simply by the character being in a state of holding or not holding an object. In other words, if you set a pick up watch for an object while `target` is already holding that object, the watch will fire immediately, and likewise for a drop watch. The value of the `object` parameter is irrelevant for drop watches — the watch will fire as soon as the character is not holding an object regardless of which object they were holding previously. `param` is the object ID for pick up watches and `-1` for drop watches.

### SetTimeAction

- **Obfuscated name:** C47
- **Availability:** all versions
- **Arguments:**
  - `receiver` (CHID) — character to receive the `TimeOut` callback
  - `caller` (CHID) — character ID forwarded to the callback as context
  - `delay` (float) — seconds to wait before firing
- **Returns:** none
- **Description:** Schedules a deferred `TimeOut` callback after `delay` seconds, delivering both receiver and caller IDs to the handler. Used for dialogue timeouts and scripted pauses during walking/event scenes. A delay of `-1` clears the timeout. Event mode `EVENT_TIMEOUT` must be enabled for the receiver.

### SetExtraAction

- **Obfuscated name:** C48
- **Availability:** all versions
- **Arguments:** none
- **Returns:** none
- **Description:** Does nothing. Original purpose unknown.

### ClearFrontEvent

- **Obfuscated name:** S00
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID, or `-1` / `#ONESELF`) — character to clear, or a global/init form
- **Returns:** none
- **Description:** Clears the character's pending/queued frontmost event so a fresh dialogue or scripted action can run cleanly. Commonly called in `mapoutend.sol` initialization and in walker/event handlers before kicking off a new sequence.

### SetPosLineAction

- **Obfuscated name:** C49
- **Availability:** all versions
- **Arguments:**
  - `id` (int) — line index, 0-11
  - `x` (float, or `#INIT`) — destination X (or `#INIT` to clear)
  - `y` (float) — destination Y
  - `z` (float) — destination Z
  - `limit` (float) — radius of the bounding box
- **Returns:** none
- **Description:** Position-anchored line/patrol action — like `SetLineAction` but referenced to an absolute world point rather than to a character. Used by the walker system to define patrol waypoints (e.g. in `walkerfunc.sol`). There are 12 slots for pos line actions, selected by the `id` argument. Fires `PosJoin` / `PosLeave` when a character enters/leaves the bounding volume (the character must have event mode `EVENT_POSBORDERLINE` enabled). Pass `#INIT` for the X argument to clear the action.

### GetDamageKind

- **Obfuscated name:** C4A
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — the character who dealt the damage
- **Returns:** (DAMAGE) — damage type: `#DAMAGE_WEAPON` (0), `#DAMAGE_KICK` (1), `#DAMAGE_OBJECT` (2)
- **Description:** Reads the type of damage just dealt by a character. Typically called inside a `Damage` callback to branch on attack method (weapon vs. kick vs. thrown object).

### GetCharVisible

- **Obfuscated name:** C4B
- **Availability:** all versions
- **Arguments:**
  - `viewer` (CHID) — the character attempting to see the target
  - `target` (CHID) — the character who the viewer is attempting to see
  - `fov` (int) — the viewer's FOV in degrees
- **Returns:** (bool) — whether `target` is visible to `viewer`
- **Description:** Checks whether `viewer` can see `target`. This checks both that `target` is inside the FOV and that there is no geometry between them blocking line of sight.

### SetLineViewAction

- **Obfuscated name:** C4C
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to configure; `#ONESELF` allowed
  - `fov` (int) — the character's FOV in degrees
  - `boundingBox` (float) — radius of the view bounding box
  - `verticalRange` (float, optional) — maximum vertical distance the character can see; default 5.0
- **Returns:** none
- **Description:** Configures a character's sight detection. With `#EVENT_LINEVIEW` enabled, fires `ViewJoin` when a target enters the sight radius and `ViewLeave` on exit. Note that the bounding volume is a cube, not a sphere. Due to the bounding volume test, `verticalRange` only has an effect if it is less than `boundingBox`. The character must have line of sight to the target (i.e. there must not be other objects blocking their view of the target). Distinct from `SetLineAction` (character-anchored with no view check) and `SetPosLineAction` (position-anchored).

### SetPadAction

- **Obfuscated name:** C4D
- **Availability:** all versions
- **Arguments:**
  - `button` (BTN) — the button to press
- **Returns:** none
- **Description:** Simulates a button press. Only the face buttons are supported.

### SetCharSayDeadFlag

- **Obfuscated name:** C4E
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to flag; `#ONESELF` allowed
  - `enabled` (bool) — `#ON` to enable, `#OFF` to disable
- **Returns:** none
- **Description:** Sets the "say dead" flag on a character. When the character dies with this flag enabled, the engine fires the global `SayDead` callback (in addition to the regular `Dead` callback), allowing custom dying-words/post-mortem scripting. Used for major characters (e.g. Hose in p02/e02, Doujima in p02/e18). This flag also controls whether a dead character is allowed to speak at all — without it, a `Say` call on a dead character has no effect.

### SePlay

- **Obfuscated name:** C4F
- **Availability:** all versions
- **Arguments:**
  - `soundId` (int) — sound-effect ID
  - `volume` (int) — volume (0–255 range observed)
  - `charId` (CHID, optional) — anchor sound to a character for spatial audio
  - `x, y, z` (float, optional) — anchor sound at a world position (alternative to `charId`)
- **Returns:** none
- **Description:** Plays a sound effect. Supports both character-anchored and positional 3D audio via the optional trailing arguments. Companions: `BGMPlay` (music), `VoicePlay` (voice lines).

### BGMPlay

- **Obfuscated name:** C50
- **Availability:** all versions
- **Arguments:**
  - `trackId` (int) — BGM track ID; `0` switches to automatic mode (Japanese comment BGM:自動モード)
  - `fadeIn` (int, optional) — fade-in duration; typical value `75`
  - `volume` (int, optional) — volume; typical value `256`
- **Returns:** none
- **Description:** Plays a BGM track, optionally fading in. Pass `0` for `trackId` to return to the engine's automatic-mode selection. Typical call: `$BGMPlay 3, 75, 256` for a battle theme. Companions: `BGMStop`, `SePlay`, `VoicePlay`.

### BGMStop

- **Obfuscated name:** C51
- **Availability:** all versions
- **Arguments:**
  - `fadeOut` (int, optional) — fade-out duration in frames; omitted = stop immediately
- **Returns:** none
- **Description:** Stops the current BGM, optionally fading out over the specified duration. Used during map transitions and event endings. Inverse of `BGMPlay`.

### VoicePlay

- **Obfuscated name:** C52
- **Availability:** all versions
- **Arguments:**
  - `voiceId` (int) — voice-line ID
  - `volume` (int, optional) — volume (0–255)
  - `charId` (CHID, optional) — character to anchor the voice spatially
- **Returns:** none
- **Description:** Plays a voice line. With a character argument, the voice plays from that character's position. Example: `$VoicePlay 682, 100, #CHID_MOKICHI`. Companions: `SePlay`, `BGMPlay`.

### Include

- **Obfuscated name:** S01
- **Availability:** all versions
- **Arguments:**
  - `filename` (string) — script file to include (with extension, e.g. `"assign.h"`)
- **Returns:** none
- **Description:** Pulls another script file into the current script, making its definitions available. The PSP version preserves `Include` statements (e.g. `$Include "assign.h";` in `config.h`); in older releases the preprocessor inlined them, so the original include structure isn't recoverable from the script source.

### Stop

- **Obfuscated name:** S02
- **Availability:** all versions
- **Arguments:** none
- **Returns:** none
- **Description:** Halts the current script's execution task — acts as a clean terminator for an event/handler scope. Japanese comments at call sites use 実行タスクを切る ("cut the execution task"). Typically the last statement of an event-handler function.

### SetWait

- **Obfuscated name:** S03
- **Availability:** all versions
- **Arguments:**
  - `seconds` (float) — duration to sleep
- **Returns:** none
- **Description:** Pauses the script for `seconds`. Use `SetWaitEndTask` instead when you need to block until a specific task (motion, dialogue) finishes rather than for a fixed duration.

### SetWaitEndTask

- **Obfuscated name:** S04
- **Availability:** all versions
- **Arguments:**
  - `taskId` (int) — task ID returned by a task-producing call (`Say`, `SetCharMotion`, `SetCharMove`, `SetCharAction`, …)
- **Returns:** none
- **Description:** Blocks the script until the specified task completes, then resumes. Idiomatic pairing: `#tid | $Say ...; $SetWaitEndTask #tid;` to await dialogue completion. Companions: `SetWait` (fixed duration), `DelTaskID` (cancel a task).

### SetNoBlock

- **Obfuscated name:** S05
- **Availability:** all versions
- **Arguments:**
  - `unknown` (int)
- **Returns:** none
- **Description:** _Unused in scripts; to be reverse-engineered. Name suggests a non-blocking mode toggle for the wait/task system._

### SetPadMode

- **Obfuscated name:** C53
- **Availability:** all versions
- **Arguments:**
  - `movement` (bool) — `#ON` to enable player movement/combat input, `#OFF` to disable
  - `camera` (bool) — `#ON` to enable player camera input, `#OFF` to disable
  - `_extra` (bool, optional) — third arg seen in some cutscenes; purpose unclear
- **Returns:** none
- **Description:** Enables/disables player gamepad input. Called `#OFF, #OFF` during cutscenes to freeze the player (Japanese comment パッドＯＦＦにする, "turn off the pad"), then restored at the end. Often combined with `SetCharStop` and `SetAIAllStop` to fully freeze the scene.

### SetPadCtrl

- **Obfuscated name:** C54
- **Availability:** all versions
- **Arguments:**
  - `enable` (int) — vibration enable flag (0 or 1)
  - `pattern` (int) — vibration pattern/mode (typically 1)
  - `duration` (float) — rumble duration in seconds
  - `intensity` (int) — rumble strength (0–255)
- **Returns:** none
- **Description:** Controls controller rumble (DualShock vibration on PS2). Used at dramatic impact moments — observed in p01/e03 and p02/e02 during player-hit beats, alongside `MTAS_DYING01` and SE. Japanese comment パッドぶるぶる ("pad rumble"). Distinct from `SetPadMode`, which controls input.

### ScreenEffect

- **Obfuscated name:** C55
- **Availability:** all versions
- **Arguments:**
  - `effect` (EFFECT) — effect type (e.g. plain fade, white fade)
  - `mode` (int) — transition mode (e.g. `-1` init, `1` fade-in, `2` fade-out)
  - `style` (int) — style/curve variant
  - `duration` (int, optional) — duration in frames
- **Returns:** none
- **Description:** Applies a fullscreen overlay effect — fades, white-outs, color washes — used for scene transitions and dramatic beats. Argument ordering (effect / direction / style / duration) is consistent across versions, though specific constants beyond fade variants are not all enumerated in the script source.

### SetDispDraw

- **Obfuscated name:** C56
- **Availability:** all versions
- **Arguments:**
  - `unknown` (int)
- **Returns:** none
- **Description:** _Unused in scripts; to be reverse-engineered. Name suggests toggling some HUD/display rendering._

### GetSamuraiValue

- **Obfuscated name:** C57
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to query (typically `#CHID_SHUJINKO`)
- **Returns:** (int) — the character's samurai value (侍度)
- **Description:** Reads the player's (or another character's) samurai value — an honor/karma stat that drives NPC reactions and difficulty. Scripts branch on thresholds, e.g. ≤ −5 triggers maximum reinforcements, ≤ 10 reduced, > 10 disables them. Heavily used across walker scripts and event info handlers. A corresponding `SetSamuraiValue` exists but is unused in script source.

### SetSamuraiValue

- **Obfuscated name:** C58
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to modify (typically `#CHID_SHUJINKO`)
  - `value` (int) — value to set
- **Returns:** none
- **Description:** Sets the character's samurai value to `value`.

### AddSamuraiValue

- **Obfuscated name:** C59
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to modify (typically `#CHID_SHUJINKO`)
  - `amount` (int) — value to add
- **Returns:** none
- **Description:** Increases the character's samurai value (侍度) by `amount` — used to reward honorable actions. Comments at call sites use forms like 侍度：+2. Companions: `SubSamuraiValue`, `GetSamuraiValue`.

### SubSamuraiValue

- **Obfuscated name:** C5A
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to modify
  - `amount` (int) — value to subtract
- **Returns:** none
- **Description:** Decreases the character's samurai value — used to penalize dishonorable actions (attacking the defenseless, etc.). Inverse of `AddSamuraiValue`; read via `GetSamuraiValue`. The Japanese comment block 侍度の加算・減算 ("samurai value add/subtract") often groups these two calls.

### GetBattleValue

- **Obfuscated name:** C5B
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to query
- **Returns:** (int) — the character's battle value
- **Description:** Gets the character's battle value. The function of battle value is unknown.

### SetBattleValue

- **Obfuscated name:** C5C
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to modify
  - `value` (int) — value to set
- **Returns:** none
- **Description:** Sets the character's battle value. The function of battle value is unknown.

### GetMapTimeID

- **Obfuscated name:** C5D
- **Availability:** all versions
- **Arguments:** none
- **Returns:** (TIME) — the current time of day
- **Description:** Get the current time of day.

### SetMapTimeID

- **Obfuscated name:** C5E
- **Availability:** all versions
- **Arguments:**
  - `timeId` (TIME) — time of day (`#TIME_MORNING`, `#TIME_AFTERNOON`, `#TIME_EVENING`, etc.)
- **Returns:** none
- **Description:** Sets the time of day for the active map/event. Typically called inside `MapOut` handlers (alongside `SetMapID` and `SetMapExitID`) to configure the destination's temporal context for the next scene.

### GetMapID

- **Obfuscated name:** C5F
- **Availability:** all versions
- **Arguments:** none
- **Returns:** (MAPID) — current map
- **Description:** Returns the currently active map ID (e.g. `#MAPID_HASHI`, `#MAPID_SHUKUBA`). Used for conditional branches at script startup. Inverse of `SetMapID`.

### SetMapID

- **Obfuscated name:** C60
- **Availability:** all versions
- **Arguments:**
  - `mapId` (MAPID) — destination map
- **Returns:** none
- **Description:** Queues a transition to the specified map. Typically called inside `MapOut` handlers alongside `SetMapExitID`, `SetMapTimeID`, `SetPhaseID`, and `SetEventID` to configure the next scene. Heavily used (140+ sites across all versions).

### GetMapExitID

- **Obfuscated name:** C61
- **Availability:** all versions
- **Arguments:** none
- **Returns:** (int) — exit slot the player used to leave the previous map
- **Description:** Returns which exit/entrance slot was used. Used on map arrival to position the player at the correct spawn point and configure the entry camera (Japanese comment 出口番号（カメラのセットに利用）"exit number; used for camera setup"). Inverse of `SetMapExitID`.

### SetMapExitID

- **Obfuscated name:** C62
- **Availability:** all versions
- **Arguments:**
  - `exitId` (int) — exit/entrance slot for the upcoming map transition
- **Returns:** none
- **Description:** Records which entrance the player will arrive at on the next map. Set inside `MapOut` along with `SetMapID`; the engine combines map + exit slot via an internal routing table to pick the destination event.

### GetEventID

- **Obfuscated name:** C63
- **Availability:** all versions
- **Arguments:** none
- **Returns:** (int) — the current event ID
- **Description:** Gets the ID of the current game event.

### SetEventID

- **Obfuscated name:** C64
- **Availability:** all versions
- **Arguments:**
  - `eventId` (int) — game-event ID within the current phase (selects an `eNN` event directory)
- **Returns:** none
- **Description:** Selects which game event will execute next within the active phase. Used alongside `SetPhaseID` and `SetMapID` to configure the next scene before `EventStart`/`EventEnd`. Not to be confused with the per-character `EVENT_*` modes managed by `SetEventMode`.

### GetPhaseID

- **Obfuscated name:** C65
- **Availability:** all versions
- **Arguments:** none
- **Returns:** (int) — current phase number (0–5)
- **Description:** Reads the current story phase (0–5). Used pervasively to gate phase-dependent behavior and dialogue. Japanese comments label it 現在フェーズ把握 ("grasp current phase").

### SetPhaseID

- **Obfuscated name:** C66
- **Availability:** all versions
- **Arguments:**
  - `phaseId` (int) — phase to switch to (0–5)
- **Returns:** none
- **Description:** Advances the game to the specified phase. Called in `MapOut` handlers (when returning to the overworld) and at main entry points (`main03_01.sol` sets phase 3; MapWalk main sets phase 0).

### SetPlayerFooting

- **Obfuscated name:** C67
- **Availability:** all versions
- **Arguments:**
  - `footing` (FOOTING) — player's faction alignment (e.g. `#FOOTING_KURONAMA`, `#FOOTING_AKADAMA`, `#FOOTING_SHUKUBA`, `#FOOTING_EVENT`, `#FOOTING_PLAYER`)
- **Returns:** none
- **Description:** Sets the player's faction alignment, controlling NPC ally/enemy AI behavior toward `CHID_SHUJINKO`. The dedicated player counterpart to `SetCharGroupID` (which targets any character).

### GetPlayerFooting

- **Obfuscated name:** C68
- **Availability:** all versions
- **Arguments:** none
- **Returns:** (FOOTING) — player's faction alignment
- **Description:** Gets the player's faction alignment.

### SetAddEventScript

- **Obfuscated name:** C69
- **Availability:** all versions
- **Arguments:**
  - `scriptList` (array) — a `list` whose first element is the phase folder name (e.g. `"p02"`) and remaining elements are event-script filenames (no `.sol`) to attach to the active game-event
- **Returns:** none
- **Description:** Registers event-level scripts onto the currently active game-event. Called in `MapIn` after `ReadEventCharList`; loads the named event scripts so their global handlers (`Init`, `Start`, `MapOut`, etc.) run at game-event scope. Typically the script list is indexed off the current phase ID. Distinct from `SetAddCharScript` (per-character scripts).

### SetAddCharScript

- **Obfuscated name:** C6A
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to attach the script to
  - `scriptName` (string) — script filename, case-insensitive, no `.sol` extension
- **Returns:** none
- **Description:** Attaches a behavior script to a single NPC. Example: `$SetAddCharScript $#CHID_DONA, "Dona";` loads `dona.sol` onto Dona. For batch attachment, see `SetAddCharScriptList`.

### SetAddCharScriptList

- **Obfuscated name:** C6B
- **Availability:** all versions
- **Arguments:**
  - `scriptName` (string) — script filename, case-insensitive, no `.sol`
  - `charIds...` (CHID, variadic) — characters to attach the script to
- **Returns:** none
- **Description:** Attaches the same behavior script to multiple NPCs at once. Example: `$SetAddCharScriptList "Zako", $#CHID_KUROZAKO1_0, $#CHID_KUROZAKO1_1;` loads `zako.sol` onto both characters.

### SetVarInt

- **Obfuscated name:** C6C
- **Availability:** all versions
- **Arguments:**
  - `slot` (int) — persistent integer variable slot ID
  - `value` (int) — value to store
- **Returns:** none
- **Description:** Writes a value into a global persistent integer slot — the game's main mechanism for cross-event flags and counters (see `docs/jp/vars.md` for known slot meanings, e.g. slot 99 / 120 for various gate flags). Read via `GetVarInt`. The string-typed variant `SetVarString` exists but is unused in scripts.

### GetVarInt

- **Obfuscated name:** C6D
- **Availability:** all versions
- **Arguments:**
  - `slot` (int) — persistent integer variable slot ID
- **Returns:** (int) — stored value
- **Description:** Reads a value from a global persistent integer slot. Idiomatic: `$#CharNum | $GetVarInt 30`. Inverse of `SetVarInt`.

### SetVarString

- **Obfuscated name:** C6E
- **Availability:** all versions
- **Arguments:**
  - `slot` (int) — persistent string variable slot ID
  - `value` (string) — value to store
- **Returns:** none
- **Description:** Writes a value into a global persistent string slot.

### GetVarString

- **Obfuscated name:** C6F
- **Availability:** all versions
- **Arguments:**
  - `slot` (int) — persistent string variable slot ID
- **Returns:** (string) — stored value
- **Description:** Reads a value from a global persistent string slot.

### SendFunc

- **Obfuscated name:** C70
- **Availability:** all versions
- **Arguments:**
  - `scope` (int) — `1` for global scope, `2` for character scope
  - `target` (CHID, or `0`) — character receiver when `scope=2`; ignored (`0`) for global
  - `funcName` (string) — name of a zero-argument function to invoke on the target script
- **Returns:** none
- **Description:** Replaces the script running in the target slot with one whose entry point is `funcName`, starting execution from the beginning. Whatever was previously running at that slot is discarded. Use during initial setup, when the target has no meaningful script running yet (e.g. `$SendFunc 2, #AA, "Living_Init"` inside `$#Init`), or as a terminal state transition where the prior behavior is meant to be abandoned (e.g. `$SendFunc 1, 0, "Battle_Func"` to flip the slot into combat mode). When the target needs to *resume* its prior behavior after the called function returns, use `SendFunc2` instead.

### SendFunc2

- **Obfuscated name:** C71
- **Availability:** all versions
- **Arguments:**
  - `scope` (int) — `1` for global scope, `2` for character scope
  - `target` (CHID, or `0`) — character receiver when `scope=2`; ignored (`0`) for global
  - `funcName` (string) — name of a zero-argument function to invoke on the target script
- **Returns:** none
- **Description:** Pushes `funcName` as a new scope onto the target script's call stack and schedules it to run on the target's next interpreter tick; when it returns, the prior scope resumes. Use this when the target is already executing a script that should continue afterward — e.g. notifying still-running characters of a death event (`$SendFunc2 2, #AKA_1A, "AfterDead"` in `walkerfunc.sol`) or invoking a per-tick handler on a character mid-idle-behavior (`$SendFunc2 2, #TUKONIN_1, "Entry"` in `p02/e05`). The function name is re-parsed as a one-line script on the target's interpreter, so it **cannot take arguments** — share data through globals or `SetVarInt` instead. Differs from a direct call in that (a) it runs on the target's interpreter rather than the caller's, (b) the call is deferred to the target's next tick rather than synchronous, and (c) `funcName` is resolved against the target's scope chain, not the caller's.

### SetCinemaScope

- **Obfuscated name:** C72
- **Availability:** all versions
- **Arguments:**
  - `enabled` (bool) — whether to enable the letterbox effect
- **Returns:** none
- **Description:** Enables or disables the letterbox effect.

### SetFontColor

- **Obfuscated name:** C73
- **Availability:** all versions
- **Arguments:**
  - `r` (int) — red channel, 0-255
  - `g` (int) — green channel, 0-255
  - `b` (int) — blue channel, 0-255
- **Returns:** none
- **Description:** Sets the dialogue text color.

### SetSerifWindowColor

- **Obfuscated name:** C74
- **Availability:** all versions
- **Arguments:**
  - `r` (int) — red channel, 0-255
  - `g` (int) — green channel, 0-255
  - `b` (int) — blue channel, 0-255
- **Returns:** none
- **Description:** Sets the dialogue window background color.

### SetSerifFrameColor

- **Obfuscated name:** C75
- **Availability:** all versions
- **Arguments:**
  - `r` (int) — red channel, 0-255
  - `g` (int) — green channel, 0-255
  - `b` (int) — blue channel, 0-255
- **Returns:** none
- **Description:** Sets the dialogue window border color.

### SetFilePath

- **Obfuscated name:** C76
- **Availability:** all versions
- **Arguments:**
  - `path` (string) — base directory for subsequent asset/script lookups (e.g. `"script/samurai/"`)
- **Returns:** none
- **Description:** Sets the working directory used for asset and script path resolution from this point on. Called at the top of main entry scripts (Japanese comment パス設定 "path setting"). Typical values: `"script/MapWalk/"`, `"script/samurai/"`, `"script/SingleTest/Yusa/"`.

### ReadEventCharList

- **Obfuscated name:** C77
- **Availability:** all versions
- **Arguments:**
  - `lstList` (array) — a `list` whose first element is the phase folder name (e.g. `"p00"`) and remaining elements are `eNN.lst` filenames (no extension) that configure characters for the event
- **Returns:** none
- **Description:** Loads and runs the character-setup `.lst` script for the current event — populates the cast, positions, and per-character behavior scripts. Called inside `MapIn` (indexed by the current phase ID) immediately before `SetAddEventScript` and `EventStart`.

### SetEventUseCharList

- **Obfuscated name:** C78
- **Availability:** all versions
- **Arguments:**
  - `charIds...` (CHID, variadic) — characters that will participate in this event
- **Returns:** none
- **Description:** Declares which characters are "in use" for the current event. Called inside event `.lst` files (e.g. p02/e01/e01.lst) to register the cast. Typically followed by per-character `SetAddCharScript` calls to attach behaviors.

### EventStart

- **Obfuscated name:** S06
- **Availability:** all versions
- **Arguments:** none
- **Returns:** none
- **Description:** Begins the currently configured game event. Called inside `MapIn` after `SetPhaseID`, `SetEventID`, `SetMapID`, `ReadEventCharList`, and `SetAddEventScript` have set the stage. Japanese comments in main.sol describe the flow: マップ読み込み → イベントの$Start呼び出し → フェードイン開始 → 1Pパッドオン.

### EventEnd

- **Obfuscated name:** S07
- **Availability:** all versions
- **Arguments:** none
- **Returns:** none
- **Description:** Ends the current game event and triggers the fade-out / next-`MapIn` chain. Inverse of `EventStart`. Idiomatically called immediately after `SetMapID`/`SetEventID` have queued up the next scene. Japanese comments: 1Pパッドオフ → メインの$MapIn呼び出し → フェードアウト開始.

### LoadExecFile

- **Obfuscated name:** C79
- **Availability:** all versions
- **Arguments:**
  - `filename` (string) — script file to execute (with extension, e.g. `"playerpos.sol"`)
- **Returns:** none
- **Description:** Loads and runs a script file in its own execution context. Unlike `Include` (which inlines definitions into the current scope), `LoadExecFile` runs the named file as a separate task. Commonly used in `MapIn` to invoke `"playerpos.sol"` for entry-point positioning.

### SetMoney

- **Obfuscated name:** C7A
- **Availability:** all versions
- **Arguments:**
  - `amount` (int) — value to set the player's money to (overwrites)
- **Returns:** none
- **Description:** Assigns the player's money (kozeni) to an absolute value. Used at initialization and to reset balances (e.g. p02/e02 after a forced-payment scene). Companions: `GetMoney` (read), `AddMoney` (increment + UI message), `SubMoney` (decrement + UI message).

### GetMoney

- **Obfuscated name:** C7B
- **Availability:** all versions
- **Arguments:** none
- **Returns:** (int) — current player money
- **Description:** Reads the player's current money balance. Used to gate purchases and other money-conditioned interactions.

### AddMoney

- **Obfuscated name:** C7C
- **Availability:** all versions
- **Arguments:**
  - `amount` (int) — yen to add to the player's wallet
  - `message` (string) — UI notification text (e.g. `"３円∮手に入れた"` = 「３円、手に入れた」; `∮` is the custom font code for `、` — see `text-encoding.md`)
- **Returns:** none
- **Description:** Awards money and shows a notification. Heavily used in event/walker scripts for rewards (1–120 yen typical). Pure-state mutation without UI uses `SetMoney`.

### SubMoney

- **Obfuscated name:** C7D
- **Availability:** all versions
- **Arguments:**
  - `amount` (int) — yen to deduct
  - `message` (string) — UI notification text (e.g. `"６円∮支払ηた"` = 「６円、支払った」 — see `text-encoding.md`)
- **Returns:** none
- **Description:** Deducts money and shows a notification. Used for fees, extortion, information-broker payments. Inverse of `AddMoney`.

### SetGameOver

- **Obfuscated name:** C7E
- **Availability:** all versions
- **Arguments:** none
- **Returns:** none
- **Description:** Triggers the game-over state. Contrast with `SetGameClear` (story success).

### Reboot

- **Obfuscated name:** C7F
- **Availability:** all versions
- **Arguments:** none
- **Returns:** none
- **Description:** Restarts the game session. This does not reboot the console itself. Exact behavior appears to depend on the game state at the time of the call. If called during gameplay, prompts the user to either continue the game or save and return to the title screen. Called internally by `SetGameStop`, `SetGameClear`, and `GameStopWait`.

### SetEventManFlag

- **Obfuscated name:** C80
- **Availability:** all versions
- **Arguments:**
  - `flagId` (int) — management-flag slot ID
  - `value` (int) — value to store (commonly `#ON`/`#OFF`, sometimes an `#EVENTPRO_*` constant)
- **Returns:** none
- **Description:** Writes an event "management" flag — a persistent per-flag slot scoped above any single event. Used for ad-hoc one-time state (e.g. `$SetEventManFlag 63, #ON` marks a Chelsea-related gate). Companion: `GetEventManFlag`. See `docs/jp/flags.md` for known slot IDs.

### GetEventManFlag

- **Obfuscated name:** C81
- **Availability:** all versions
- **Arguments:**
  - `flagId` (int) — management-flag slot ID
- **Returns:** (int) — current value (boolean or `#EVENTPRO_*` value)
- **Description:** Reads a management flag. Used to gate event routes (e.g. flag 14 for the shared ending; flag 35 for location-transition completion). Cataloged in `docs/jp/flags.md`. Inverse: `SetEventManFlag`.

### SetEventProFlag

- **Obfuscated name:** C82
- **Availability:** all versions
- **Arguments:**
  - `eventId` (int) — event whose progress is being recorded
  - `state` (EVENTPRO) — `#EVENTPRO_NULL` / `#EVENTPRO_RETURN` / `#EVENTPRO_STOP` / `#EVENTPRO_END`
- **Returns:** none
- **Description:** Writes a structured progress state for the given event — used to drive event flow (continue, suspend, end). Companion: `GetEventProFlag`. Distinct from the more freeform `SetEventManFlag`.

### GetEventProFlag

- **Obfuscated name:** C83
- **Availability:** all versions
- **Arguments:**
  - `eventId` (int) — event to query
- **Returns:** (EVENTPRO) — progress state (`#EVENTPRO_NULL` 0 / `#EVENTPRO_RETURN` 1 / `#EVENTPRO_STOP` 2 / `#EVENTPRO_END` 3)
- **Description:** Reads the event's progress flag. Branches off this drive whether an event re-runs, resumes, or stays complete.

### SetEventActEndFlag

- **Obfuscated name:** C84
- **Availability:** all versions
- **Arguments:**
  - `flagId` (int) — act-end flag slot
  - `value` (int) — `#ON` to mark complete, `#OFF` to clear
- **Returns:** none
- **Description:** Marks one of a small set of "act end" completion flags — used for one-time milestones such as tutorial completion (p00/e02 sets slot 0; `main.sol` checks it to skip the tutorial next launch) or shortcut unlocks. Persistent across sessions.

### GetEventActEndFlag

- **Obfuscated name:** C85
- **Availability:** all versions
- **Arguments:**
  - `flagId` (int) — act-end flag slot
- **Returns:** (bool) — `#ON` if set, `#OFF` if not
- **Description:** Reads an act-end flag. Used to gate one-time content and persistent shortcuts (e.g. `#MIHARI_END_FLAG`, `#SHORTCUT_DONA`).

### SetHintMessage

- **Obfuscated name:** C86
- **Availability:** all versions
- **Arguments:**
  - `message` (string) — hint text; `\n` supported for line breaks; empty string clears the hint
- **Returns:** none
- **Description:** Displays a contextual on-screen hint/tooltip (e.g. 敵を全滅させよ。 "Defeat all enemies"). Accepts either string literals or variables containing localized text (`#Selif0`, etc.). Heavily used across all phases.

### SetGameStop

- **Obfuscated name:** C87
- **Availability:** all versions
- **Arguments:** none
- **Returns:** none
- **Description:** Used during event transitions to ask the player whether they want to save and quit or continue playing. Called after completing the tutorial and after time-of-day transitions (`SetMapTimeID`).

### SetGameClear

- **Obfuscated name:** C88
- **Availability:** all versions
- **Arguments:** none
- **Returns:** none
- **Description:** Marks the game as successfully cleared. Called in final phase-5 events (p05/e16, e19, e24, e26), immediately after `SetEventManFlag` writes an ending-identifier into flag 47 (one of seven endings). Contrast with `SetGameOver`.

### SetDrawCost

- **Obfuscated name:** C89
- **Availability:** all versions
- **Arguments:**
  - `cost` (int) — draw-cost / LOD budget value
- **Returns:** none
- **Description:** Adjusts the rendering budget — appears to control LOD/culling during expensive scenes. Used before cinematic movement in p04/e16 (e.g. `$SetDrawCost 200`). Exact units unclear from script context.

### LoadMessage

- **Obfuscated name:** C8A
- **Availability:** all versions
- **Arguments:** none
- **Returns:** none
- **Description:** Unknown. Called immediately after `SetGameScriptPhase` in a hard-coded script triggered by `EventEndWait`.

### SetGameScriptPhase

- **Obfuscated name:** C8B
- **Availability:** all versions
- **Arguments:** none
- **Returns:** none
- **Description:** Unknown. Called immediately before `LoadMessage` in a hard-coded script triggered by `EventEndWait`.

### GetValue2String

- **Obfuscated name:** C8C
- **Availability:** all versions
- **Arguments:**
  - `value` (int) — value to format
- **Returns:** (string) — decimal string representation
- **Description:** Converts an integer to its decimal string form for use in dialogue and UI. Idiom: `#moneyString : $GetValue2String #money;`. Found in katuage/tubo and similar shop/extortion scripts.

### DelTaskID

- **Obfuscated name:** C8D
- **Availability:** all versions
- **Arguments:**
  - `taskId` (int) — task ID returned by an async-producing call (`Say`, `SetCharMotion`, `SetCharMove`, `SetCharAction`, `SetCharFace`, `SetCharNeckAction`, `SetCharDirFollow`, …)
- **Returns:** none
- **Description:** Cancels the async task with the given ID. Common pattern: capture the ID (`#tid | $SetCharFace ...`), then call `$DelTaskID #tid` before kicking off a replacement. Pair-companion: `SetWaitEndTask` (block until done).

### GiveMeDaikon

- **Obfuscated name:** C8E
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to give the "daikon" to
- **Returns:** none
- **Description:** Decrements the character's daikon flag and causes them to drop a healing item. The character's daikon flag must be non-zero, otherwise there is no effect. Called inside dialogue branches that condition on the donor's daikon flag (e.g. `?i (#num ge 3) { $GiveMeDaikon #target }`). Tied to the `*CharDaikonFlag` family. Despite the name, the healing item dropped is not a radish (`OBJ_DAIKON`, restores 300 HP) but rather a chick uiro (`OBJ_HIYOKO`, fully restores HP).

### SetWeaponForge

- **Obfuscated name:** C8F
- **Availability:** all versions
- **Arguments:**
  - `forgeType` (int) — `0` = attack-up, `1` = defense-up, `2` = random, `3` = hardness (never called with this value; `SetWeaponHardness` is used instead, which has the same effect)
- **Returns:** none
- **Description:** Applies a forge enhancement to the player's equipped weapon at the foundry. Japanese comments at call sites label the three modes: 攻撃力上昇 / 防御力上昇 / ランダム上昇. Companion: `SetWeaponHardness` (硬度上昇).

### SetWeaponHardness

- **Obfuscated name:** C90
- **Availability:** all versions
- **Arguments:** none
- **Returns:** none
- **Description:** Increases the equipped weapon's hardness/durability (硬度上昇). Called as part of weapon-upgrade flows at the foundry, alongside `SetWeaponForge`.

### SetWeaponDeposit

- **Obfuscated name:** C91
- **Availability:** all versions
- **Arguments:** none
- **Returns:** none
- **Description:** Deposits the player's currently equipped sword to the weapon collection — the engine half of the Doujima "send my sword in" handover. Called immediately after `SetEventManFlag 27` is set to mark the weapon as sent.

### GetWeaponNum

- **Obfuscated name:** C92
- **Availability:** all versions
- **Arguments:** none
- **Returns:** (int) — number of weapons in the player's deposit collection
- **Description:** Returns how many weapons the player currently has on deposit. Used in all Doujima dialogues to gate options: when `≥ 2`, additional forge/hardness menu choices appear; otherwise only "new deposit" is offered.

### CheckWeaponHardness

- **Obfuscated name:** C93
- **Availability:** all versions
- **Arguments:** none
- **Returns:** (int) — hardness level (0–3), or `-1` if the equipped weapon is broken
- **Description:** Reports the equipped weapon's hardness tier. Used in Doujima dialogues to validate weapon condition before allowing a forge or hardness operation. Companion to `SetWeaponHardness`.

### CheckWeaponAttack

- **Obfuscated name:** C94
- **Availability:** all versions
- **Arguments:** none
- **Returns:** (bool) — `#ON` if attack/sharpness can still be increased, `#OFF` if at max
- **Description:** Checks whether the equipped weapon still has room to be sharpened. Used to gate the forge-attack option in Doujima menus.

### CheckWeaponDefense

- **Obfuscated name:** C95
- **Availability:** all versions
- **Arguments:** none
- **Returns:** (bool) — `#ON` if defense/pliability can still be increased, `#OFF` if at max
- **Description:** Checks whether the equipped weapon can still be made more pliable. Used to gate the forge-defense option in Doujima menus, with the refusal line その刀はこれ以上しなやかに出来ないぞ ("This sword cannot be made any more pliable") played on `#OFF`.

### ReportWeapon

- **Obfuscated name:** C96
- **Availability:** all versions
- **Arguments:** none
- **Returns:** (int) — task ID for the message-display
- **Description:** Displays a UI message reporting the equipped weapon's current stats. Called immediately after `SetWeaponForge` or `SetWeaponHardness` to announce the result. Return value is typically captured and awaited via `SetWaitEndTask`.

### EventEndWait

- **Obfuscated name:** C97
- **Availability:** all versions
- **Arguments:** none
- **Returns:** none
- **Description:** Unknown. Called asynchronously by `EventEnd`. Asynchronously calls `MapIn`, `SetGameScriptPhase`, and `LoadMessage`.

### GameStopWait

- **Obfuscated name:** C98
- **Availability:** all versions
- **Arguments:** none
- **Returns:** none
- **Description:** Unknown. Called asynchronously by `SetGameStop`. Behavior appears identical to `EventEndWait` except that it does not call `MapIn` and it calls `Reboot` in place of `SetGameScriptPhase` + `LoadMessage`.

### SetMapOutEnd

- **Obfuscated name:** C99
- **Availability:** us_proto, us, kanzenban, psp (added in the North American release)
- **Arguments:** none
- **Returns:** none
- **Description:** Finalizes a map-out transition, signaling that the `MapOut` cutscene/cleanup has completed. Called at the tail of `mapoutend.sol` scripts after character movement and camera adjustments. Works in concert with the earlier `SetMapID` / `SetMapExitID` / `SetEventID` setup.

### PrintFunc

- **Obfuscated name:** C9B
- **Availability:** all versions
- **Arguments:** none
- **Returns:** none
- **Description:** Does nothing. Presumably some kind of debug utility compiled out of release builds of the game, but not the basic print function since `print` exists. Perhaps it printed debug information about functions.

### SetAIChar

- **Obfuscated name:** C9C
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to configure; `#ONESELF` allowed
  - `aiState` (AI) — AI mode (e.g. `#AI_CHASE`, `#AI_BATTLE`, `#AI_APPROACH`, `#AI_MOVE`, `#AI_NONCOM_IDLE`, `#AI_TAKEUP`)
  - `groupId` (int, optional) — an AI group to assign the character to; defaults to `0`
- **Returns:** none
- **Description:** Assigns or updates a character's autonomous AI state. Companions: `GetAIChar` (read), `DelAIChar` (clear). Typically combined with `SetCharTarget` (combat focus) or `SetAITargetItem` / `SetAITargetPos` (objects/positions). `groupId` is an arbitrary integer that identifies which AI group a character belongs to. AI groups can be associated with a faction via `SetAIGroupFooting` and assigned to target one another with `SetAITargetGroup`.

### GetAIChar

- **Obfuscated name:** C9D
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to query
- **Returns:** (AI) — the character's current AI state
- **Description:** Reads a character's current AI state. Used to branch on whether they're idle, in combat, chasing, etc. Companion to `SetAIChar`.

### DelAIChar

- **Obfuscated name:** C9E
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character whose AI to clear
- **Returns:** none
- **Description:** Disables a character's AI — they stop autonomous behavior until re-armed with `SetAIChar`. Commonly used in `NpcOut` handlers after hiding a departing character.

### SetAITargetGroup

- **Obfuscated name:** C9F
- **Availability:** all versions
- **Arguments:**
  - `group1` (int) — the group that will target the other group
  - `group2` (int) — the AI group that will be the first group's target; `-1` clears the target
  - `flag` (int) — `1` for combat target (attack on sight), `0` for non-hostile target
- **Returns:** none
- **Description:** Configures one AI group to target another. Used alongside `SetAIGroupRelation` and `SetAIChar` during battle setup (e.g. p02/e20/tubo.sol).

### SetAIAllStop

- **Obfuscated name:** CA0
- **Availability:** all versions
- **Arguments:**
  - `enabled` (bool) — `#ON` to freeze all AI, `#OFF` to resume
- **Returns:** none
- **Description:** Pauses/resumes AI logic for all NPCs on the current map (Japanese comment 通行人処理, "passerby processing"). Frequently combined with `SetPadMode #OFF, #OFF` to freeze both the player and the world during cutscenes.

### SetAISiegeLimit

- **Obfuscated name:** CA1
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to configure
  - `limit` (float) — siege/approach distance limit in game units
- **Returns:** none
- **Description:** Sets how close an AI character will close in on its target before stopping (the "siege" radius). Companion to `SetAIBackLimit`, `SetAIRunLimit`, `SetAIWalkLimit`.

### SetAIBackLimit

- **Obfuscated name:** CA2
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to configure
  - `limit` (float) — backstep/retreat distance limit
- **Returns:** none
- **Description:** Sets the maximum distance the AI will retreat/backstep during combat. Often called through a helper like `SetCharLimit` that bundles back/walk/run/siege limits together.

### SetAIWalkLimit

- **Obfuscated name:** CA3
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to configure
  - `limit` (float) — walk-distance limit
- **Returns:** none
- **Description:** Sets the AI's walk-distance threshold. Member of the back/walk/run/siege limit family that controls NPC pacing in combat and patrol.

### SetAIRunLimit

- **Obfuscated name:** CA4
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to configure
  - `limit` (float) — run-distance limit
- **Returns:** none
- **Description:** Sets how far the AI will sprint before reverting to walking or stopping. Highest tier in the back/walk/run/siege movement-limit family.

### SetAITargetItem

- **Obfuscated name:** CA5
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to direct
  - `objId` (OBJ) — world object to pursue
- **Returns:** none
- **Description:** Directs an AI character to seek out and interact with a specific object. Typically paired with an `AI_TAKEUP`-style mode: `SetAIChar #char, #AI_TAKEUP, 3; SetAITargetItem #char, #OBJ_ISU_A;`.

### SetAITargetPos

- **Obfuscated name:** CA6
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to direct; `#ONESELF` allowed
  - `x` (float) — destination X
  - `y` (float) — destination Y
  - `z` (float) — destination Z
- **Returns:** none
- **Description:** Sends an AI character to a specific world position. Usually configured alongside `#AI_MOVE` via `SetAIChar` and the `SetAI*Limit` family.

### SetAICharMove

- **Obfuscated name:** CA7
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to move; `#ONESELF` allowed
  - `motion` (COMMAND) — typically `#COMMAND_WALK` or `#COMMAND_RUN`
  - `x` (float) — destination X
  - `y` (float) — destination Y
  - `z` (float) — destination Z
- **Returns:** none
- **Description:** AI-managed counterpart to `SetCharMove`. Always uses absolute XYZ coordinates (no character-relative form), and does not return a task ID — it integrates with the character's AI rather than producing a discrete task.

### SetAIGroupFooting

- **Obfuscated name:** CA8
- **Availability:** all versions
- **Arguments:**
  - `groupId` (int) — AI group
  - `footing` (FOOTING) — faction the AI group is treated as
- **Returns:** none
- **Description:** Maps an AI group to a faction footing, deciding how its members behave with respect to other factions' relations. Operates at the group level rather than per-character (compare `SetCharGroupID`, `SetPlayerFooting`).

### SetAIRugbyBall

- **Obfuscated name:** CA9
- **Availability:** all versions
- **Arguments:**
  - `ball` (OBJ) — object to use as the rugby ball
- **Returns:** none
- **Description:** Sets the object considered the ball by characters in the `AI_RUGBY` AI mode. This is part of a simple rugby minigame that exists in the game code but is not used by any scripts in any released build of the game.

### SetAIGroupRelation

- **Obfuscated name:** CAA
- **Availability:** all versions
- **Arguments:**
  - `groupA` (FOOTING) — source faction
  - `groupB` (FOOTING) — target faction
  - `relation` (int) — `#NO_RELATION` (0), `#ENEMY_RELATION` (1), or `#FRIEND_RELATION` (2)
- **Returns:** none
- **Description:** Sets faction A's relationship toward faction B. The relation is directional, so to establish a mutual relationship you must call it again with the factions swapped. Companion: `GetAIGroupRelation`.

### GetAIGroupRelation

- **Obfuscated name:** CAB
- **Availability:** all versions
- **Arguments:**
  - `groupA` (FOOTING) — source faction
  - `groupB` (FOOTING) — target faction
- **Returns:** (int) — `#NO_RELATION` / `#ENEMY_RELATION` / `#FRIEND_RELATION`
- **Description:** Reads faction A's current relationship toward faction B. Idiomatic: `#rel | $GetAIGroupRelation #FOOTING_KURONAMA, #FOOTING_PLAYER`.

### Say

- **Obfuscated name:** CAC
- **Availability:** all versions
- **Arguments:**
  - `speaker` (CHID) — speaking character; `#ONESELF` allowed
  - `listener` (CHID) — character being addressed
  - `text` (string) — dialogue text (`\n` for newlines)
  - `endDelay` (float) — time in seconds to wait after speaking the line before dismissing the dialogue box
  - `charTime` (int) — delay between characters in 30ths of a second
  - `sayType` (SAY) — say-style/dialogue box shape (e.g. `#SAY_NORMAL`, `#SAY_SHARP`)
  - `startDelay` (float, optional) — a delay in seconds before starting to speak
- **Returns:** (int) — task ID
- **Description:** The primary dialogue function. Idiom: `#tid | $Say ...; $SetWaitEndTask #tid;` to block until the line finishes. Pair with `SetSayPos` for subtitle placement and `SetSayMotion` for accompanying motion overrides; for multi-listener variants see `SayGroup`. Note that the game adds 1 to the provided value of `charTime`. The total time in frames that the dialogue box is visible for is `endDelay * 60 + (charTime * 2 + 1) * len(text)`.

### SetSayMotion

- **Obfuscated name:** CAD
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to animate
  - `motion` (int) — motion / expression override; special values include `#SAY_WEAPON_ON` (2048) and `#SAY_WEAPON_OFF` (2049)
  - `enabled` (bool) — `#ON` to apply, `#OFF` to disable
- **Returns:** none
- **Description:** Overrides the motion played by a character while speaking. Used alongside `Say` for special cases — e.g. drawing/sheathing the sword mid-line via `SAY_WEAPON_ON`/`SAY_WEAPON_OFF`.

### SetTalkSelect

- **Obfuscated name:** CAE
- **Availability:** all versions
- **Arguments:**
  - `talker` (CHID, or `#INIT`) — character offering the dialogue choices, or `#INIT` to reset
  - `choices...` (string, variadic) — zero or more option strings
- **Returns:** none
- **Description:** Presents a list of dialogue choices to the player. The player's selection fires the global `TalkSelect` callback (with the chosen index). Pass `#INIT` to reset/clear pending choices.

### SayGroup

- **Obfuscated name:** CAF
- **Availability:** all versions
- **Arguments:**
  - `listener` (CHID) — listener
  - `text` (string) — dialogue
  - `endDelay` (float) — time in seconds to wait after speaking the line before dismissing the dialogue box
  - `charTime` (int) — delay between characters in 30ths of a second
  - `sayType` (SAY) — say-style/dialogue box shape
  - `speakers...` (CHID, variadic) — characters who speak the line
- **Returns:** none
- **Description:** Like `Say`, but allows multiple characters to speak a line in unison — useful for group reactions. Example: `$SayGroup #CHID_TESHIN, "おう！", 1.0, 1, #SAY_SHARP, #CHID_KUROZAKO1_1, #CHID_KUROZAKO3_2, #CHID_KUROZAKO3_3`. See `Say` for notes on `charTime`. Unlike `Say`, there is no `startDelay` argument; the start delay is always 0.

### SetSayPos

- **Obfuscated name:** CB0
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character whose subtitle position is being set
  - `x` (int) — screen-space X
  - `y` (int) — screen-space Y
- **Returns:** none
- **Description:** Sets the screen position of the speaker's dialogue subtitle. Called alongside `Say` to lay out multi-character conversations without overlapping text (observed ranges: 0–480 X, 0–272 Y).

### SetMapOutSelect

- **Obfuscated name:** CB1
- **Availability:** us_proto, us, kanzenban, psp (added in the North American release)
- **Arguments:**
  - `options` (string, variadic) — the options to select from
- **Returns:** (int) — task ID for the prompt
- **Description:** Presents the player with a list of options to select from when leaving a map. Used in hard-coded scripts to implement the early exit (leaving Rokkotsu Pass without completing the story). Calling with no options clears the select mode.

### GetObjChar

- **Obfuscated name:** CB2
- **Availability:** all versions
- **Arguments:**
  - `charId` (CHID) — character to query
- **Returns:** (OBJ, or `-1`) — object currently held by the character, or `-1` if none
- **Description:** Reports which world object a character is currently holding. Commonly used to guard `SetCharRelObj` (only release if holding something) and to branch on which object is held. Inverse of `SetCharHoldObj`.

### SetObjPos

- **Obfuscated name:** CB3
- **Availability:** all versions
- **Arguments:**
  - `objId` (OBJ) — object to position
  - `x` (float) — world X
  - `y` (float) — world Y
  - `z` (float) — world Z
- **Returns:** none
- **Description:** Teleports a dynamic world object to absolute coordinates. The object-side counterpart to `SetCharPos`. Used during map setup and cutscenes to position props such as `#OBJ_UBAGURUMA`, `#OBJ_KINKO`, `#OBJ_ISU_A`.

### AddObjPos

- **Obfuscated name:** CB4
- **Availability:** all versions
- **Arguments:**
  - `objId` (OBJ) — object to nudge
  - `dx` (float) — X delta
  - `dy` (float) — Y delta
  - `dz` (float) — Z delta
- **Returns:** none
- **Description:** Offsets an object's position by a delta — like `SetObjPos`, but additive against the current position. Used for incremental nudges (e.g. adjusting prop placement during animations).

### GetObjRangeChar

- **Obfuscated name:** CB5
- **Availability:** all versions
- **Arguments:**
  - `objId` (OBJ) — object to test
  - `charId` (CHID) — character to test against
  - `distance` (float) — distance threshold in game units
- **Returns:** (bool) — `#ON` if within `distance`, else `#OFF`
- **Description:** Proximity check between an object and a character. Mirror of `GetCharRange` for the OBJ side. Used to gate object interactions (e.g. p03/e14 tests `#OBJ_KINKO` against Dona at 20.0 then 1.0 units before allowing acquisition).

### SetObjDraw

- **Obfuscated name:** CB6
- **Availability:** all versions
- **Arguments:**
  - `objId` (OBJ) — object to show/hide
  - `visible` (bool) — `#ON` to show, `#OFF` to hide
- **Returns:** none
- **Description:** Toggles object visibility on the current map. Object-side counterpart to `SetCharDraw`. Used to make props appear/disappear during cutscenes and event transitions.

### SetObjAction

- **Obfuscated name:** CB7
- **Availability:** all versions
- **Arguments:**
  - `objId` (OBJ) — object to act on
- **Returns:** none
- **Description:** Triggers an object's built-in action animation/state transition. Unlike `SetCharAction` (which takes a command + parameter), `SetObjAction` plays each object's single predefined behavior — e.g. `$SetObjAction #OBJ_TSUKUE` topples a desk.

### SetObjMoveTetudo

- **Obfuscated name:** CB8
- **Availability:** all versions
- **Arguments:**
  - `enabled` (bool) — `#ON` to start the train, `#OFF` to stop
- **Returns:** none
- **Description:** Drives the railway-crossing train (汽車) on `#MAPID_TETUDO`. Called during map setup to start the train's movement animation along the track.

### SetObjRestore

- **Obfuscated name:** CB9
- **Availability:** all versions
- **Arguments:** none
- **Returns:** none
- **Description:** Restores all world objects on the current map to their initial-placement state. Japanese comments label call sites as オブジェクト初期配置 ("object initial placement") — used at event initialization to reset any prop disturbance from prior play.

### LoadObjSceneData

- **Obfuscated name:** CBA
- **Availability:** all versions
- **Arguments:**
  - `setId` (OBJECT_SET) — scene-specific object-set identifier (e.g. `#OBJECT_SET_MONN_CLOSE`, `#OBJECT_SET_KINKO`, `#OBJECT_SET_TAIHOU`, `#OBJECT_SET_TUTORIAL`)
- **Returns:** none
- **Description:** Loads a predefined scene's set of world objects and their initial placements. Each `OBJECT_SET_*` constant selects one `.Iom`/`.Iob` placement file hardcoded in the executable (e.g. `#OBJECT_SET_KINKO` → `Object/Yashiki/Yashiki_Kinko.Iom`, which places `OBJ_KINKO` at a fixed transform). See `docs/object-placement.md` for the full constant→file mapping and file format. Often immediately followed by per-object positioning or animation calls.

### SetObjStop

- **Obfuscated name:** CBB
- **Availability:** all versions
- **Arguments:**
  - `objId` (OBJ) — object to stop
- **Returns:** none
- **Description:** Stops an object's animation/action. Inverse of `SetObjAction`.

### SetObjTaihouAction

- **Obfuscated name:** CBC
- **Availability:** all versions
- **Arguments:**
  - `cannonId` (int) — zero-based index of the cannon to fire
- **Returns:** none
- **Description:** Fires a cannon (大砲, taihou). Used in phase-5 battle sequences (e14/e16/e17/e19) immediately after `LoadObjSceneData` loads the cannon set (`#OBJECT_SET_*_TAIHOU`). Pair-companion: `SetObjTaihouStop`.

### SetObjTaihouStop

- **Obfuscated name:** CBD
- **Availability:** all versions
- **Arguments:**
  - `cannonId` (int) — cannon to silence
- **Returns:** none
- **Description:** Stops a firing cannon. Called when the player engages cannon operators (`CHID_YAKUNIN_*`) to silence the cannon during the fight. Inverse of `SetObjTaihouAction`.

### SetNoMapOutFlag

- **Obfuscated name:** CBE
- **Availability:** us_proto, us, kanzenban, psp (added in the North American release)
- **Arguments:**
  - `enabled` (bool) — `#ON` to prevent map exit, `#OFF` to allow
- **Returns:** none
- **Description:** Locks/unlocks the player on the current map. When set, the `MapOut` callback checks this flag and short-circuits the transition, trapping the player while a cutscene or critical event resolves. Read via `GetNoMapOutFlag`. The flag is cleared automatically by the engine on map transition, immediately before `MapIn`. In versions without this function, int var 104 or local variables are used for the same purpose (without the automatic reset on `MapIn`).

### GetNoMapOutFlag

- **Obfuscated name:** CBF
- **Availability:** us_proto, us, kanzenban, psp (added in the North American release)
- **Arguments:** none
- **Returns:** (bool) — `#ON` if exit is locked, `#OFF` otherwise
- **Description:** Reads the current state of the no-map-out lock. Companion to `SetNoMapOutFlag`.

### SetDemoEnd

- **Obfuscated name:** _(no obfuscation in the demo build)_
- **Availability:** demo only
- **Arguments:** none
- **Returns:** none
- **Description:** Ends the demo and returns to the title screen. Called from `#TaikenBan_End` ("trial-version end") handlers in demo events e01/e02/e03/e20, typically after a short `$SetWait 0.5` to let the closing line play out. Not present in any retail release.

### GetVSRand

- **Obfuscated name:** _(no obfuscation in the PSP build)_
- **Availability:** psp only
- **Arguments:**
  - `range` (int) — the range of numbers to be returned
- **Returns:** (int) — the random number
- **Description:** Returns a random number between `0` and `range - 1`. This is ostensibly intended for use in the PSP-exclusive online versus mode and uses a different RNG than `random`.
