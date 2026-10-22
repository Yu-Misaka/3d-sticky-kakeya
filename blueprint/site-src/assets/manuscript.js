'use strict';
// Proofs are closed <details>. Open the one a link points to, and offer to open them all.
(() => {
  function reveal() {
    let target = null;
    try { target = location.hash && document.getElementById(decodeURIComponent(location.hash.slice(1))); } catch (_) { return; }
    for (let element = target; element; element = element.parentElement) {
      if (element.tagName === 'DETAILS' && element.classList.contains('proof')) element.open = true;
    }
    if (target) target.scrollIntoView({ block: 'start' });
  }
  const proofs = Array.from(document.querySelectorAll('details.proof'));
  const heading = document.querySelector('.ms-text h1');
  if (proofs.length && heading) {
    const button = document.createElement('button');
    button.className = 'all-proofs';
    const label = () => { button.textContent = proofs.every(proof => proof.open) ? 'Fold all proofs' : `Open all ${proofs.length} proofs`; };
    button.addEventListener('click', () => { const open = !proofs.every(proof => proof.open); for (const proof of proofs) proof.open = open; label(); });
    for (const proof of proofs) proof.addEventListener('toggle', label);
    label();
    heading.after(button);
  }
  // Only one badge list is open at a time; Escape or a click elsewhere closes it.
  const pops = Array.from(document.querySelectorAll('details.pop'));
  document.addEventListener('click', event => { for (const pop of pops) if (!pop.contains(event.target)) pop.open = false; });
  document.addEventListener('keydown', event => { if (event.key === 'Escape') for (const pop of pops) pop.open = false; });
  window.addEventListener('hashchange', reveal);
  reveal();
})();
