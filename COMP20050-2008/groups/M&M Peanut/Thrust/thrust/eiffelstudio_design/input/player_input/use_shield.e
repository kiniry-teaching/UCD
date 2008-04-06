indexing
	description: "Use the spaceships shield to protect itself or to gather fuel."

class
	USE_SHIELD

inherit
	KEYBOARD_INPUT

feature -- Queries
	keycode: CHARACTER is
		once
			Result := ' '
		end

feature -- Commands

invariant -- Constraints
	-- The keycode for using the shield is always ' ' (space).
	keycode_is_space: keycode = ' '

end
