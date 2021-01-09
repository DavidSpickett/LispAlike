(import "lib/lib.lal")

# str is the text to encode, key is the shift distance
(defun 'encode 'str 'key
  (let
    # All input should be one of these chars, or a space
    'alphabet (map + "ABCDEFGHIJKLMNOPQRSTUVWXYZ")
    (accumulate
      (lambda 'encoded 'c
        (+
          encoded
          (if
            # Leave spaces unencoded
            (eq c " ") c
            (let 'new_idx
              (%
                # Shift the letter by the key
                (+ (index c alphabet) key)
                # Keep it in range of the alphabet
                26
              )
              (nth
                # If the new index is <0, wrap around to the end
                (if (< new_idx 0)
                  (+ 26 new_idx)
                  new_idx
                )
                alphabet
              )
            )
          )
        )
      )
      str ""
    )
  )
)

(defun 'find_key 'str 'expected
  (letrec
    # Only need one non space char since shift is always the same
    'in (findif (lambda 'c (neq c " ")) str)
    'exp (nth (index in str) expected)
    'try_key
    (lambda 'key
      # Assuming that there's always a valid key
      (cond
        # Found the key
        (eq in (encode exp key)) key
        # More keys left to try
        true (try_key (+ key 1))
      )
    )
    (try_key 0)
  )
)

(letrec 'plain   "HELLO WORLD"
        'key 34
        'encoded (encode plain key)
  (body
    (print plain "=>" encoded)
    (print encoded "=>" (encode encoded (- 0 key)))
  )
)

# Space at the start to show we pick a non space char
# to test for the key.
(letrec 'plain " AARDVARK PYJAMAS"
        'key 85
        'encoded (encode plain key)
        'found_key (find_key encoded plain)
  (body
    (print plain "=>" encoded)
    (print "with key" key "aka" (% key 26))
    (print "Found key:" found_key)
    (print encoded "=>" (encode encoded (- 0 found_key)))
  )
)

## "HELLO WORLD" "=>" "PMTTW EWZTL"
## "PMTTW EWZTL" "=>" "HELLO WORLD"
## " AARDVARK PYJAMAS" "=>" " HHYKCHYR WFQHTHZ"
## "with key" 85 "aka" 7
## "Found key:" 7
## " HHYKCHYR WFQHTHZ" "=>" " AARDVARK PYJAMAS"
## Return value: none
