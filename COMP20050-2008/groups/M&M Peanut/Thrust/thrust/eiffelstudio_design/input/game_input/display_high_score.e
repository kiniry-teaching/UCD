indexing
	description: "Display the high score table."

class
	DISPLAY_HIGH_SCORE

inherit
	KEYBOARD_INPUT

feature -- Queries
	keycode: CHARACTER is
		once
			Result := ' '
		end

feature -- Commands

invariant -- Constraints
	-- The keycode for looking at the high score list is always ' ' (space).
	keycode_is_space: keycode = ' '

end
