/**
 * Modern Index Page Initialization
 * Pure JavaScript implementation with enhanced features
 */

setThemeColor();

// API endpoints
const TMPLINK_API_USER = 'https://tmp-api.vx-cdn.com/api_v2/user';
const TMPLINK_API_TOKEN = 'https://tmp-api.vx-cdn.com/api_v2/token';

// Track current button state for language switching
let currentButtonState = 'login'; // 'login' or 'continue'

// Initialize area detection and redirect for China mainland users
initAreaDetection();

// Initialize when app is ready
app.ready(() => {
    initializeHomepage();
});

/**
 * Initialize the modern homepage
 */
function initializeHomepage() {
    const lang = app.languageSetting;
    langset(lang);
    app.languageBuild();
    
    // Update page metadata
    document.title = app.languageData.title_index;
    document.querySelector('meta[name=description]').setAttribute('content', app.languageData.des_index);
    
    // Initialize components
    initNativeDropdown();
    initThemeToggle();
    initScrollEffects();
    initIntersectionObserver();
    initMenubarXTracking();
    autoLogin();
    sendAnalytics();
    
    // Ensure all sections are visible
    ensureSectionsVisible();
}

/**
 * Initialize theme toggle functionality
 */
function initThemeToggle() {
    const themeToggle = document.getElementById('theme-toggle');
    const body = document.body;
    
    if (!themeToggle) return;
    
    // Check local storage theme preference
    const savedTheme = localStorage.getItem('theme-preference');
    const systemPrefersDark = window.matchMedia('(prefers-color-scheme: dark)').matches;
    
    // Initialize theme
    if (savedTheme) {
        // User has manually set theme
        body.classList.add('theme-manual');
        if (savedTheme === 'dark') {
            body.classList.add('dark-mode');
        }
    } else if (systemPrefersDark) {
        // No manual setting, but system prefers dark mode
        body.classList.add('dark-mode');
    }
    
    // Toggle theme
    themeToggle.addEventListener('click', () => {
        const isDarkMode = body.classList.contains('dark-mode');
        
        if (isDarkMode) {
            // Switch to light mode
            body.classList.remove('dark-mode');
            body.classList.add('theme-manual');
            localStorage.setItem('theme-preference', 'light');
            updateThemeColor('#ffffff');
        } else {
            // Switch to dark mode
            body.classList.add('dark-mode');
            body.classList.add('theme-manual');
            localStorage.setItem('theme-preference', 'dark');
            updateThemeColor('#1f2937');
        }
        
        // Add toggle animation effect
        themeToggle.style.transform = 'scale(0.9)';
        setTimeout(() => {
            themeToggle.style.transform = 'scale(1)';
        }, 150);
    });
    
    // Listen for system theme changes (only effective when no manual setting)
    const mediaQuery = window.matchMedia('(prefers-color-scheme: dark)');
    function handleSystemThemeChange(e) {
        if (!body.classList.contains('theme-manual')) {
            if (e.matches) {
                body.classList.add('dark-mode');
                updateThemeColor('#1f2937');
            } else {
                body.classList.remove('dark-mode');
                updateThemeColor('#ffffff');
            }
        }
    }
    
    if (mediaQuery.addEventListener) {
        mediaQuery.addEventListener('change', handleSystemThemeChange);
    } else if (mediaQuery.addListener) {
        mediaQuery.addListener(handleSystemThemeChange);
    }
    
    // Reset theme preference function (optional)
    window.resetThemePreference = function() {
        localStorage.removeItem('theme-preference');
        body.classList.remove('theme-manual', 'dark-mode');
        // Recheck system preference
        if (window.matchMedia('(prefers-color-scheme: dark)').matches) {
            body.classList.add('dark-mode');
            updateThemeColor('#1f2937');
        } else {
            updateThemeColor('#ffffff');
        }
    };
}

/**
 * Update theme color meta tag
 */
function updateThemeColor(color) {
    const themeColorMeta = document.querySelector('meta[name="theme-color"]');
    if (themeColorMeta) {
        themeColorMeta.setAttribute('content', color);
    }
}

/**
 * Initialize native dropdown functionality
 */
function initNativeDropdown() {
    const languageToggle = document.getElementById('language-toggle');
    const languageSelector = document.querySelector('.language-selector');
    const dropdown = document.getElementById('language-dropdown');
    
    if (!languageToggle || !languageSelector || !dropdown) return;
    
    // Toggle dropdown on button click
    languageToggle.addEventListener('click', (e) => {
        e.stopPropagation();
        languageSelector.classList.toggle('active');
    });
    
    // Close dropdown when clicking outside
    document.addEventListener('click', (e) => {
        if (!languageSelector.contains(e.target)) {
            languageSelector.classList.remove('active');
        }
    });
    
    // Close dropdown when pressing Escape
    document.addEventListener('keydown', (e) => {
        if (e.key === 'Escape') {
            languageSelector.classList.remove('active');
        }
    });
    
    // Close dropdown after selecting language
    const dropdownItems = dropdown.querySelectorAll('.dropdown-item');
    dropdownItems.forEach(item => {
        item.addEventListener('click', () => {
            languageSelector.classList.remove('active');
        });
    });
}

/**
 * Initialize area detection for China mainland users
 */
function initAreaDetection() {
    const xhr = new XMLHttpRequest();
    xhr.open('POST', TMPLINK_API_TOKEN, true);
    xhr.setRequestHeader('Content-Type', 'application/x-www-form-urlencoded');
    
    xhr.onreadystatechange = () => {
        if (xhr.readyState === XMLHttpRequest.DONE) {
            if (xhr.status === 200) {
                const rsp = JSON.parse(xhr.responseText);
                if (rsp.data === 1) {
                    handleChinaMainlandRedirect();
                }
            }
        }
    };
    
    const params = new URLSearchParams();
    params.append('action', 'set_area');
    xhr.send(params.toString());
}

/**
 * Handle redirect for China mainland users
 */
function handleChinaMainlandRedirect() {
    if (window.location.hostname !== 'www.ttttt.link' && window.location.hostname !== '127.0.0.1') {
        const params = window.location.search || '';
        window.location.href = 'https://www.ttttt.link' + params;
    }
}

/**
 * Initialize scroll effects for modern interactions
 */
function initScrollEffects() {
    let ticking = false;
    
    function updateScrollEffects() {
        const scrollTop = window.pageYOffset || document.documentElement.scrollTop;
        
        // Hide/show language selector based on scroll position
        const languageBtn = document.getElementById('translater-btn');
        if (languageBtn) {
            if (scrollTop > 300) {
                languageBtn.style.display = 'none';
            } else {
                languageBtn.style.display = 'block';
            }
        }
        
        // Parallax effect for hero section
        const hero = document.getElementById('hero');
        if (hero && scrollTop < window.innerHeight) {
            const parallaxSpeed = 0.5;
            hero.style.transform = `translateY(${scrollTop * parallaxSpeed}px)`;
        }
        
        ticking = false;
    }
    
    function requestTick() {
        if (!ticking) {
            requestAnimationFrame(updateScrollEffects);
            ticking = true;
        }
    }
    
    window.addEventListener('scroll', requestTick, { passive: true });
}

/**
 * Initialize Intersection Observer for animation triggers
 */
function initIntersectionObserver() {
    // Skip if user prefers reduced motion
    if (window.matchMedia('(prefers-reduced-motion: reduce)').matches) {
        return;
    }
    
    // Skip if IntersectionObserver is not supported
    if (!window.IntersectionObserver) {
        return;
    }
    
    const observerOptions = {
        root: null,
        rootMargin: '0px 0px -100px 0px',
        threshold: 0.1
    };
    
    const observer = new IntersectionObserver((entries) => {
        entries.forEach(entry => {
            if (entry.isIntersecting) {
                entry.target.classList.add('animate-in');
                
                // Add staggered animation for feature boxes
                if (entry.target.classList.contains('feature-box')) {
                    const siblings = Array.from(entry.target.parentElement.children);
                    const delay = siblings.indexOf(entry.target) * 100;
                    entry.target.style.animationDelay = `${delay}ms`;
                }
            }
        });
    }, observerOptions);
    
    // Observe elements that should animate in
    const animateElements = document.querySelectorAll('.feature-box, .about-content, .feature-row');
    animateElements.forEach(el => {
        observer.observe(el);
    });
}

/**
 * Initialize MenubarX tracking
 */
function initMenubarXTracking() {
    if (localStorage.getItem('from_menubarx') === null) {
        const url = new URL(location.href);
        const s = url.searchParams.get('s');
        
        if (s === 'mx') {
            localStorage.setItem('from_menubarx', '1');
        } else {
            localStorage.setItem('from_menubarx', '0');
        }
    }
}

/**
 * Set language and update UI
 */
function langset(lang) {
    const langMap = {
        'en': 'English',
        'cn': '简体中文',
        'hk': '繁体中文',
        'jp': '日本語'
    };
    
    const selectedLangElement = document.querySelector('.selected_lang');
    if (selectedLangElement) {
        selectedLangElement.textContent = langMap[lang] || 'English';
    }
    
    app.languageSet(lang);
    
    // Wait for language data to be loaded, then update button text
    setTimeout(() => {
        updateButtonLanguage();
    }, 100);
}

/**
 * Navigate to login/workspace
 */
function Login() {
    // Add smooth transition effect
    document.body.style.opacity = '0.7';
    document.body.style.transition = 'opacity 0.3s ease';
    
    setTimeout(() => {
        const url = '/?tmpui_page=/app&listview=preload';
        location.href = url;
    }, 150);
}

/**
 * Auto-login functionality with modern UI feedback
 */
async function autoLogin() {
    const apiToken = localStorage.getItem('app_token');
    const startButton = document.querySelector('#index_start');
    
    if (!startButton) return;
    
    // Show modern loading state
    showLoadingState(startButton);
    
    if (apiToken) {
        try {
            const response = await fetch(TMPLINK_API_USER, {
                method: 'POST',
                headers: {
                    'Content-Type': 'application/x-www-form-urlencoded'
                },
                body: new URLSearchParams({
                    action: 'get_detail',
                    token: apiToken
                })
            });
            
            if (response.ok) {
                const responseData = await response.json();
                if (responseData.status === 1) {
                    // User is logged in, show continue button instead of auto-redirect
                    showContinueButton(startButton);
                } else {
                    showLoginButton(startButton);
                }
            } else {
                showLoginButton(startButton);
            }
        } catch (error) {
            console.error('Login request failed:', error);
            showLoginButton(startButton);
        }
    } else {
        showLoginButton(startButton);
    }
}

/**
 * Show loading state with modern spinner
 */
function showLoadingState(element) {
    element.innerHTML = `
        <div class="loading-container">
            <div class="modern-spinner"></div>
        </div>
    `;
}

/**
 * Show success state with checkmark animation
 */
function showSuccessState(element) {
    element.innerHTML = `
        <div class="success-container">
            <div class="success-checkmark">
                <svg width="40" height="40" viewBox="0 0 24 24" fill="none" stroke="white" stroke-width="3" stroke-linecap="round" stroke-linejoin="round">
                    <path d="M9 11l3 3L22 4"></path>
                    <path d="M21 12v7a2 2 0 01-2 2H5a2 2 0 01-2-2V5a2 2 0 012-2h11"></path>
                </svg>
            </div>
        </div>
    `;
}

/**
 * Show continue button for logged-in users
 */
function showContinueButton(element) {
    currentButtonState = 'continue';
    const buttonText = app.languageData?.i2023_new_index_continue || '继续使用';
    element.innerHTML = `<a href="javascript:;" class="btn-get-started" onclick="Login()">
        <svg class="icon-svg" viewBox="0 0 24 24" style="margin-right: 0.5rem; width: 1.2em; height: 1.2em;">
            <path d="M4 11V13H16L10.5 18.5L11.92 19.92L19.84 12L11.92 4.08L10.5 5.5L16 11H4Z"/>
        </svg>
        ${buttonText}
    </a>`;
}

/**
 * Show login button with modern styling
 */
function showLoginButton(element) {
    currentButtonState = 'login';
    const buttonText = app.languageData?.i2023_new_index_getting_start || 'Get Started';
    element.innerHTML = `<a href="javascript:;" class="btn-get-started" onclick="Login()">${buttonText}</a>`;
}

/**
 * Update button text when language changes
 */
function updateButtonLanguage() {
    const startButton = document.querySelector('#index_start');
    if (startButton && startButton.innerHTML.trim() !== '') {
        // Use the tracked state to determine which button to show
        if (currentButtonState === 'continue') {
            showContinueButton(startButton);
        } else {
            showLoginButton(startButton);
        }
    }
}

/**
 * Ensure all sections are visible
 */
function ensureSectionsVisible() {
    const sections = ['#about', '#features', '#footer'];
    sections.forEach(selector => {
        const element = document.querySelector(selector);
        if (element) {
            element.style.display = 'block';
            element.style.visibility = 'visible';
            element.style.opacity = '1';
            console.log(`Section ${selector} found and made visible`);
        } else {
            console.warn(`Section ${selector} not found`);
        }
    });
    
    // Additional check for main element
    const main = document.querySelector('#main');
    if (main) {
        main.style.display = 'block';
        main.style.visibility = 'visible';
        main.style.opacity = '1';
        console.log('Main element found and made visible');
    }
}

/**
 * Send analytics data
 */
function sendAnalytics() {
    const token = localStorage.getItem('app_token');
    if (token) {
        fetch(TMPLINK_API_USER, {
            method: 'POST',
            headers: {
                'Content-Type': 'application/x-www-form-urlencoded'
            },
            body: new URLSearchParams({
                action: 'event_ui',
                token: token,
                title: 'TMPLINK - Modern Index',
                path: location.pathname + location.search
            })
        }).catch(error => {
            console.debug('Analytics request failed:', error);
        });
    }
}

/**
 * Set initial theme color (will be overridden by theme toggle)
 */
function setThemeColor() {
    const themeColorMeta = document.querySelector('meta[name="theme-color"]');
    if (!themeColorMeta) return;
    
    // Check if there's a saved theme preference
    const savedTheme = localStorage.getItem('theme-preference');
    if (savedTheme) {
        themeColorMeta.setAttribute('content', savedTheme === 'dark' ? '#1f2937' : '#ffffff');
    } else {
        // No saved preference, use system preference
        const isDarkMode = window.matchMedia('(prefers-color-scheme: dark)').matches;
        themeColorMeta.setAttribute('content', isDarkMode ? '#1f2937' : '#ffffff');
    }
}

/**
 * Enhanced error handling for graceful degradation
 */
window.addEventListener('error', (event) => {
    console.error('Index page error:', event.error);
    // Fallback to basic functionality if modern features fail
});

/**
 * Performance monitoring
 */
if ('performance' in window) {
    window.addEventListener('load', () => {
        setTimeout(() => {
            if (performance.getEntriesByType) {
                const perfData = performance.getEntriesByType('navigation')[0];
                if (perfData && perfData.loadEventEnd - perfData.loadEventStart > 3000) {
                    console.warn('Page load time exceeded 3 seconds');
                }
            }
        }, 0);
    });
}

/**
 * Add CSS animation classes when elements come into view
 */
function addAnimationClasses() {
    const elements = document.querySelectorAll('.feature-box, .about-content');
    elements.forEach(el => {
        if (!el.style.animationName) {
            el.style.animation = 'fadeInUp 0.6s ease-out forwards';
        }
    });
}

// Add animation classes after DOM is loaded
if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', addAnimationClasses);
} else {
    addAnimationClasses();
}