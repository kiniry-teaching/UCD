indexing
	description: "Toggle between hearing music or sound effects."

class
	TOGGLE_MUSIC_OR_SOUND_EFFECTS

inherit
	KEYBOARD_INPUT

feature -- Queries
	keycode: CHARACTER is
		once
			Result := 'm'
		end

feature -- Commands

invariant -- Constraints
	-- The keycode for toggling music/sound effects is always 'm'.
	keycode_is_m: keycode = 'm'

end
