"""Apply all exhaustive certificate controls to the final scored-only panel."""
from unittest.mock import patch
import scorer_checks
from register_scored import scored_rows

def main():
    with patch.object(scorer_checks, 'build_data', return_value={'test':scored_rows()}):
        scorer_checks.run()

if __name__=='__main__': main()
