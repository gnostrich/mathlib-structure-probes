#!/usr/bin/env python3
"""
Auto-Reply to Moltbook - Generic AI-Powered Reply Generator

This script automatically fetches new replies from Moltbook and responds
to them using AI-generated content. It dynamically learns about the repository
to provide contextual responses.
"""

import os
import json
import requests
import sys
from pathlib import Path
from datetime import datetime, timezone

# Configuration
MOLTHUB_API_KEY = os.environ.get('MOLTHUB_API_KEY')
OPENAI_API_KEY = os.environ.get('OPENAI_API_KEY')
GITHUB_TOKEN = os.environ.get('GITHUB_TOKEN')
GITHUB_REPOSITORY = os.environ.get('GITHUB_REPOSITORY', '')
DRY_RUN = os.environ.get('DRY_RUN', 'false').lower() == 'true'

def get_repo_context():
    """Dynamically extract repository context"""
    print("📖 Reading repository context...")
    
    context = {
        'repo_name': GITHUB_REPOSITORY,
        'readme': '',
        'description': ''
    }
    
    # Try to read README
    readme_paths = ['README.md', 'README', 'readme.md', 'Readme.md']
    for readme_path in readme_paths:
        if Path(readme_path).exists():
            try:
                with open(readme_path, 'r', encoding='utf-8') as f:
                    context['readme'] = f.read()[:2000]  # First 2000 chars
                print(f"✅ Found {readme_path}")
                break
            except Exception as e:
                print(f"⚠️ Error reading {readme_path}: {e}")
    
    # Get repo description from GitHub API if available
    if GITHUB_TOKEN and GITHUB_REPOSITORY:
        try:
            headers = {
                'Authorization': f'token {GITHUB_TOKEN}',
                'Accept': 'application/vnd.github.v3+json'
            }
            response = requests.get(
                f'https://api.github.com/repos/{GITHUB_REPOSITORY}',
                headers=headers,
                timeout=10
            )
            if response.status_code == 200:
                repo_data = response.json()
                context['description'] = repo_data.get('description', '')
                print(f"✅ Retrieved repo description from GitHub")
        except Exception as e:
            print(f"⚠️ Could not fetch repo description: {e}")
    
    return context

def fetch_replies():
    """Fetch replies from Moltbook
    
    Note: This endpoint may not exist in the Moltbook API yet.
    The function will attempt to fetch from multiple possible endpoints.
    """
    print("📥 Fetching replies from Moltbook...")
    
    headers = {
        'Authorization': f'Bearer {MOLTHUB_API_KEY}',
        'Content-Type': 'application/json'
    }
    
    # Try multiple possible endpoints
    endpoints_to_try = [
        'https://www.moltbook.com/api/v1/notifications',
        'https://www.moltbook.com/api/v1/replies',
        'https://www.moltbook.com/api/v1/mentions',
    ]
    
    for endpoint in endpoints_to_try:
        try:
            print(f"  Trying endpoint: {endpoint}")
            response = requests.get(
                endpoint,
                headers=headers,
                timeout=30
            )
            
            if response.status_code == 200:
                data = response.json()
                # Handle different response formats
                reply_list = data if isinstance(data, list) else data.get('replies', data.get('data', data.get('notifications', [])))
                if reply_list:
                    print(f"✅ Found {len(reply_list)} replies from {endpoint}")
                    return reply_list
            elif response.status_code != 404:
                print(f"  ⚠️ Endpoint returned {response.status_code}: {response.text[:100]}")
        except Exception as e:
            print(f"  ⚠️ Error accessing {endpoint}: {e}")
    
    print(f"⚠️ No valid reply endpoints found. The Moltbook API may not support automatic reply fetching yet.")
    print(f"💡 Tip: Check Moltbook directly for new replies and consider adding API endpoint support.")
    return []

def generate_ai_reply(reply_content, reply_author, repo_context):
    """Generate an AI-powered contextual reply"""
    print(f"🤖 Generating AI reply for message from {reply_author}...")
    
    # Use OpenAI if available
    if OPENAI_API_KEY:
        try:
            # Support both old and new OpenAI API versions
            try:
                # Try new API (v1.0.0+)
                from openai import OpenAI
                client = OpenAI(api_key=OPENAI_API_KEY)
                
                context_text = f"Repository: {repo_context['repo_name']}\n"
                if repo_context['description']:
                    context_text += f"Description: {repo_context['description']}\n"
                if repo_context['readme']:
                    context_text += f"\nREADME excerpt:\n{repo_context['readme']}\n"
                
                prompt = (
                    f"You are responding to a community member on Moltbook who replied to a post about this repository.\n\n"
                    f"Repository Context:\n{context_text}\n"
                    f'Their message:\n"{reply_content}"\n\n'
                    "Generate a friendly, helpful response that:\n"
                    "1. Thanks them for their interest/question\n"
                    "2. Provides useful information based on the repository context\n"
                    "3. Encourages collaboration or further discussion\n"
                    "4. Includes relevant links to the repository if appropriate\n"
                    "5. Keeps a professional but enthusiastic tone\n\n"
                    "Keep the response concise (2-3 paragraphs max)."
                )
                
                response = client.chat.completions.create(
                    model="gpt-4",
                    messages=[
                        {"role": "system", "content": "You are a helpful repository maintainer engaging with your community."},
                        {"role": "user", "content": prompt}
                    ],
                    max_tokens=300,
                    temperature=0.7
                )
                
                ai_reply = response.choices[0].message.content.strip()
                print(f"✅ AI reply generated successfully")
                return ai_reply
                
            except ImportError:
                # Fall back to old API
                import openai
                openai.api_key = OPENAI_API_KEY
                
                context_text = f"Repository: {repo_context['repo_name']}\n"
                if repo_context['description']:
                    context_text += f"Description: {repo_context['description']}\n"
                if repo_context['readme']:
                    context_text += f"\nREADME excerpt:\n{repo_context['readme']}\n"
                
                prompt = (
                    f"You are responding to a community member on Moltbook who replied to a post about this repository.\n\n"
                    f"Repository Context:\n{context_text}\n"
                    f'Their message:\n"{reply_content}"\n\n'
                    "Generate a friendly, helpful response that:\n"
                    "1. Thanks them for their interest/question\n"
                    "2. Provides useful information based on the repository context\n"
                    "3. Encourages collaboration or further discussion\n"
                    "4. Includes relevant links to the repository if appropriate\n"
                    "5. Keeps a professional but enthusiastic tone\n\n"
                    "Keep the response concise (2-3 paragraphs max)."
                )
                
                response = openai.ChatCompletion.create(
                    model="gpt-4",
                    messages=[
                        {"role": "system", "content": "You are a helpful repository maintainer engaging with your community."},
                        {"role": "user", "content": prompt}
                    ],
                    max_tokens=300,
                    temperature=0.7
                )
                
                ai_reply = response.choices[0].message.content.strip()
                print(f"✅ AI reply generated successfully")
                return ai_reply
            
        except Exception as e:
            print(f"⚠️ OpenAI API error: {e}")
            # Fall through to template
    
    # Fallback: Use contextual templates
    reply_lower = reply_content.lower()
    repo_url = f"https://github.com/{repo_context['repo_name']}"
    
    if any(word in reply_lower for word in ['collaborate', 'work together', 'interested', 'join', 'contribute']):
        return (
            f"Thanks so much for your interest in collaborating! 🎉\n\n"
            f"We'd love to have you involved with this project. "
            f"Check out the repository at {repo_url} to get started. "
            f"Feel free to open an issue with your ideas or reach out directly!\n\n"
            f"Looking forward to working together!"
        )
    
    elif any(word in reply_lower for word in ['how', 'what', 'why', 'explain', '?']):
        return (
            f"Great question! 🤔\n\n"
            f"You can find more details about this project at {repo_url}. "
            f"The README has comprehensive documentation and examples to help you get started.\n\n"
            f"Let me know if you have any other questions!"
        )
    
    else:
        return (
            f"Thanks for your comment! 👋\n\n"
            f"We're excited about this project and would love your feedback. "
            f"Check out the repository at {repo_url} for more information.\n\n"
            f"Feel free to reach out with questions or suggestions!"
        )

def post_reply(post_id, reply_content):
    """Post a reply to Moltbook"""
    if DRY_RUN:
        print(f"🔍 DRY RUN: Would post reply to {post_id}")
        print(f"Content preview: {reply_content[:150]}...")
        return True
    
    print(f"📤 Posting reply to Moltbook post {post_id}...")
    
    headers = {
        'Authorization': f'Bearer {MOLTHUB_API_KEY}',
        'Content-Type': 'application/json'
    }
    
    payload = {
        'content': reply_content
    }
    
    try:
        response = requests.post(
            f'https://www.moltbook.com/api/v1/posts/{post_id}/replies',
            headers=headers,
            json=payload,
            timeout=30
        )
        
        if response.status_code in [200, 201]:
            print(f"✅ Reply posted successfully!")
            return True
        else:
            print(f"❌ Failed to post reply: {response.status_code}")
            print(f"Response: {response.text}")
            return False
    except Exception as e:
        print(f"❌ Error posting reply: {e}")
        return False

def main():
    """Main execution"""
    print("🚀 Starting Auto-Reply to Moltbook workflow")
    print(f"⏰ Time: {datetime.now(timezone.utc).isoformat()}")
    print(f"🔧 Mode: {'DRY RUN' if DRY_RUN else 'LIVE'}")
    print(f"📦 Repository: {GITHUB_REPOSITORY}")
    print("")
    
    # Get repository context
    repo_context = get_repo_context()
    print("")
    
    # Fetch new replies
    replies = fetch_replies()
    
    if not replies:
        print("✨ No new replies to process. All caught up!")
        return 0
    
    # Process each reply
    successful_replies = 0
    failed_replies = 0
    
    for reply in replies:
        post_id = reply.get('post_id') or reply.get('id')
        content = reply.get('content', '')
        author = reply.get('author', 'Unknown')
        
        print(f"\n{'='*60}")
        print(f"Processing reply from: {author}")
        print(f"Post ID: {post_id}")
        print(f"Content: {content[:100]}...")
        print("")
        
        # Generate AI response
        ai_reply = generate_ai_reply(content, author, repo_context)
        
        print(f"\nGenerated response:")
        print(f"{ai_reply}")
        print("")
        
        # Post the reply
        if post_reply(post_id, ai_reply):
            successful_replies += 1
        else:
            failed_replies += 1
    
    # Summary
    print(f"\n{'='*60}")
    print(f"📊 Summary:")
    print(f"   Total replies processed: {len(replies)}")
    print(f"   ✅ Successful: {successful_replies}")
    print(f"   ❌ Failed: {failed_replies}")
    print(f"   🔧 Mode: {'DRY RUN' if DRY_RUN else 'LIVE'}")
    
    if failed_replies > 0:
        print(f"\n⚠️ Some replies failed. Check logs above for details.")
        return 1
    
    print(f"\n✨ Auto-reply workflow completed successfully!")
    return 0

if __name__ == '__main__':
    sys.exit(main())
