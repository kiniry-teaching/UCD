indexing
	description: "Start a game."

class
	START_GAME

inherit
	KEYBOARD_INPUT

feature -- Queries
	keycode: CHARACTER is
		once
			Result := ' '
		end

feature -- Commands

invariant -- Constraints
	-- The keycode for starting the game is always ' ' (space).
	keycode_is_m: keycode = ' '

end
